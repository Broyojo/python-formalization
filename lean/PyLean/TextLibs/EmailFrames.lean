import PyLean.TextLibs.EmailLex

/-!
The recursion limit for `get_comment`, `Comment.__str__` and `Comment.content`
(Lib/email/_header_value_parser.py, CPython 3.15.2), which recurse once per level of comment
nesting.

Calling a Python function pushes a frame: `_Py_EnterRecursivePy` (Python/ceval_macros.h:426-429)
decrements `py_recursion_remaining` and, when it was not positive, raises
`RecursionError("maximum recursion depth exceeded")` (`_Py_CheckRecursiveCallPy`,
Python/ceval.c:1026-1043); returning gives the frame back. C functions (`str` methods, `list`
methods, regular expressions, `str()` of a `str` subclass without `__str__`) push none; a class
call runs the class's Python `__new__`/`__init__`, one frame each, and a generator expression's
body one frame while it runs (list comprehensions are inlined, PEP 709).

These functions catch no `RecursionError`, so a call raises it exactly when the deepest chain of
Python calls it makes needs more frames than are left. `fooN` is that depth for `foo` on its
input, its own frame included, and `need r (fooN ..) foo` is the call made with `r` frames left
(the `r` is `py_recursion_remaining` when `foo` is called). The difftest checks these depths
against CPython: it runs each case with exactly `r` frames left.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- A call that needs `n` frames, made with `r` frames left. -/
def need {α : Type} (r n : Nat) (x : EPy α) : EPy α := if n ≤ r then x else throw .recursionError

/-- Frames of `_validate_xtext(t)` for a terminal with text `s`, :1026-1034: its own, and below
it `NonPrintableDefect(...)` when there are non-printables (`NonPrintableDefect.__init__` ->
`HeaderDefect.__init__` -> `MessageDefect.__init__`, Lib/email/errors.py:85-106), else
`utils._has_surrogates` (one frame; `UndecodableBytesDefect.__init__` is one too). -/
def validateN (s : Str) : Nat := 1 + (if (nonPrintables s).isEmpty then 1 else 3)

/-- Frames of `get_qp_ctext(value)`, :1196-1211: its own, and below it the deepest of
`_get_ptext_to_endchars` (one), `WhiteSpaceTerminal.__new__` (one) and `_validate_xtext`. -/
def qpCtextN (value : Str) : Nat :=
  match getPtextToEndchars value (fun c => c == 40 || c == 41) with
  | .ok (p, _, _) => 1 + validateN p
  | .error _ => 2

/-- Frames of `Comment()` (`TokenList.__init__`, :138-140), of `get_fws` with the
`WhiteSpaceTerminal.__new__` it calls (:1068-1078), and of `InvalidHeaderDefect(...)`
(`HeaderDefect.__init__` -> `MessageDefect.__init__`). -/
def initN : Nat := 1
def fwsN : Nat := 2
def defectN : Nat := 2

mutual
/-- Frames of `get_comment(value)`, :1286-1309, with the same fuel as `getComment`. -/
def commentN : Nat → Str → Nat
  | 0, _ => 0
  | n + 1, value =>
    if headIs (· != 40) value then 1
    else
      let fin := match commentLoop n (value.drop 1) (mkL .comment) with
        | .ok (_, []) => defectN
        | _ => 0
      1 + max initN (max (commentLoopN n (value.drop 1)) fin)
/-- Frames of the calls the loop of `get_comment` makes, :1297-1304. -/
def commentLoopN : Nat → Str → Nat
  | 0, _ => 0
  | n + 1, value =>
    match value with
    | [] => 0
    | ch :: _ =>
      if ch == 41 then 0
      else if isWsp ch then max fwsN (commentLoopN n (getFws value).2)
      else if ch == 40 then
        match getComment n value with
        | .ok (_, v) => max (commentN n value) (commentLoopN n v)
        | .error _ => commentN n value
      else
        match getQpCtext value with
        | .ok (_, v) => max (qpCtextN value) (commentLoopN n v)
        | .error _ => qpCtextN value
end

mutual
/-- Frames of `str(x)` for a comment or a terminal: `Comment.__str__` (:289-294) and, for each
element, `Comment.quote` (:296-301), which calls `str()` of a nested comment; `str()` of a
terminal is C. Only comment trees are measured here (their elements are terminals and
comments). -/
def commentStrN : Tok → Nat
  | .node .comment _ ks _ _ => 1 + quoteN ks
  | _ => 0
/-- The deepest `self.quote(x)` of `[self.quote(x) for x in self]`. -/
def quoteN : List Tok → Nat
  | [] => 0
  | k :: ks => max (1 + (if k.ty == "comment" then commentStrN k else 0)) (quoteN ks)
end

/-- The deepest `str(x)` over the elements of a comment. -/
def kidsStrN : List Tok → Nat
  | [] => 0
  | k :: ks => max (commentStrN k) (kidsStrN ks)

/-- Frames of `c.content` (:303-305): the property's frame, the generator expression's, and
`str(x)` of each element. -/
def contentN (c : Tok) : Nat := 2 + kidsStrN c.kids

/-- `get_comment(value)` with `r` frames left. -/
def getCommentR (r n : Nat) (value : Str) : EPy (Tok × Str) := need r (commentN n value) (getComment n value)

/-- `str(c)` with `r` frames left. -/
def commentStrR (r : Nat) (c : Tok) : EPy Str := need r (commentStrN c) (.ok c.str)

/-- `c.content` with `r` frames left. -/
def commentContentR (r : Nat) (c : Tok) : EPy Str := need r (contentN c) (.ok (strs c.kids))

end PyLean.TextLibs.Email
