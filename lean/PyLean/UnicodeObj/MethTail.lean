import PyLean.UnicodeObj.MethStrip

/-!
`tailmatch` (Objects/unicodeobject.c:9711-9772) and its callers: `PyUnicode_Tailmatch`
(:9775-9785), `str.startswith` (:13381-13418), `str.endswith` (:13438-13474),
`str.removeprefix` (:12664-12676) and `str.removesuffix` (:12692-12704), with their clinic
wrappers (Objects/clinic/unicodeobject.c.h).
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The middle loop of `tailmatch`, :9762-9766: `for (i = 1; i < end_sub; ++i)`, returning 0
at the first difference. -/
def tailLoop (rd rs : Int → Nat) (endSub : Int) (i : Nat) : Int :=
  if (i : Int) < endSub then
    if rd i ≠ rs i then 0 else tailLoop rd rs endSub (i + 1)
  else 1
termination_by (endSub - i).toNat

/-- `tailmatch`, unicodeobject.c:9711-9772. `PyUnicode_READ` out of `self` is `s.getD`; the
indices it reads are in range (see `TailmatchDoc`). With both strings of the same kind the
`memcmp` of :9751-9756 compares the `len(substring)` units at `offset`, which for one kind are
the characters. -/
def tailmatch (s sub : Str) (start «end» : Int) (direction : Int) : Int :=
  let (start, «end») := StrSearch.adjustIndices start «end» s.length
  let «end» := «end» - sub.length
  if «end» < start then 0
  else if sub.length = 0 then 1
  else
    let endSub : Int := sub.length - 1
    let offset := if direction > 0 then «end» else start
    let rd (i : Int) : Nat := s.getD (offset + i).toNat 0
    let rs (i : Int) : Nat := sub.getD i.toNat 0
    if rd 0 = rs 0 ∧ rd endSub = rs endSub then
      if kindWidth s = kindWidth sub then
        if StrSearch.window s offset sub.length = sub then 1 else 0
      else tailLoop rd rs endSub 1
    else 0

/-- `_PyUnicode_EnsureUnicode`, Include/internal/pycore_unicodeobject.h:96-105. -/
def ensureUnicode : Arg → Py Str
  | .str s => .ok s
  | a => .error (.typeError s!"must be str, not {a.tpName}")

/-- `PyUnicode_Tailmatch`, unicodeobject.c:9775-9785. -/
def pyUnicodeTailmatch (str substr : Arg) (start «end» : Int) (direction : Int) : Py Int := do
  let s ← ensureUnicode str
  let sub ← ensureUnicode substr
  return tailmatch s sub start «end» direction

/-- The tuple loop of `unicode_startswith_impl` (:13385-13405) and `unicode_endswith_impl`
(:13442-13461): an element that is not a `str` raises only when reached. -/
def tailTuple (name : String) (dir : Int) (s : Str) (start «end» : Int) : List Arg → Py Bool
  | [] => .ok false
  | .str sub :: rest =>
    if tailmatch s sub start «end» dir ≠ 0 then .ok true else tailTuple name dir s start «end» rest
  | a :: _ => .error (.typeError s!"tuple for {name} must only contain str, not {a.tpName}")

/-- `unicode_startswith_impl` (`name = "startswith"`, `dir = -1`) and `unicode_endswith_impl`
(`"endswith"`, `+1`). -/
def startsEndsImpl (name : String) (dir : Int) (s : Str) (subobj : Arg) (start «end» : Int) :
    Py Bool :=
  match subobj with
  | .tuple items => tailTuple name dir s start «end» items
  | .str sub => .ok (tailmatch s sub start «end» dir ≠ 0)
  | a => .error (.typeError s!"{name} first arg must be str or a tuple of str, not {a.tpName}")

/-- The clinic wrappers of `startswith`/`endswith`: `start` and `end` through
`_PyEval_SliceIndex` (defaults 0 and `PY_SSIZE_T_MAX`), in that order, before the impl. -/
def unicodeStartsEnds (name : String) (dir : Int) (s : Str) (subobj : Arg)
    (start «end» : Option Arg) : Py Bool := do
  let a ← match start with | none => pure 0 | some x => sliceIndex x 0
  let b ← match «end» with | none => pure ssizeMax | some x => sliceIndex x ssizeMax
  startsEndsImpl name dir s subobj a b

/-- `_PyArg_BadArgument(fname, "argument", "str", arg)`, Python/getargs.c:663-670. -/
def badStrArgument (fname : String) (a : Arg) : PyExc :=
  .typeError s!"{fname}() argument must be str, not {match a with | .none => "None" | _ => a.tpName}"

/-- `str.removeprefix`: the clinic `unicode` converter, then `unicode_removeprefix_impl`,
unicodeobject.c:12664-12676. -/
def unicodeRemoveprefix (s : Str) (pre : Arg) : Py Str :=
  match pre with
  | .str p =>
    let m := tailmatch s p 0 ssizeMax (-1)
    if m ≠ 0 then pyUnicodeSubstring s p.length s.length else .ok s
  | a => .error (badStrArgument "removeprefix" a)

/-- `str.removesuffix`, unicodeobject.c:12692-12704. -/
def unicodeRemovesuffix (s : Str) (suffix : Arg) : Py Str :=
  match suffix with
  | .str p =>
    let m := tailmatch s p 0 ssizeMax 1
    if m ≠ 0 then pyUnicodeSubstring s 0 ((s.length : Int) - p.length) else .ok s
  | a => .error (badStrArgument "removesuffix" a)

end PyLean.UnicodeObj
