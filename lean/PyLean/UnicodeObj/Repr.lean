import PyLean.UnicodeObj.Ctype

/-!
`unicode_repr`, Objects/unicodeobject.c:12707-12795, and `STRINGLIB(repr)`,
Objects/stringlib/repr.h:8-95. The memory layout of the output (length and
`maxch` computed by a first pass, then written by a second) is kept so that the
two passes can be compared.
-/

namespace PyLean.UnicodeObj

/-- Accumulator of the first pass: `osize`, `maxch`, `squote`, `dquote`. -/
structure ReprScan where
  osize : Nat := 0
  maxch : Nat := 127
  squote : Nat := 0
  dquote : Nat := 0
  deriving Repr, DecidableEq

/-- One iteration of the first loop, unicodeobject.c:12719-12749. -/
def reprScanStep (a : ReprScan) (ch : Nat) : ReprScan :=
  if ch = 39 then { a with squote := a.squote + 1, osize := a.osize + 1 }
  else if ch = 34 then { a with dquote := a.dquote + 1, osize := a.osize + 1 }
  else if ch = 92 ∨ ch = 9 ∨ ch = 13 ∨ ch = 10 then { a with osize := a.osize + 2 }
  else if ch < 32 ∨ ch = 0x7f then { a with osize := a.osize + 4 }
  else if ch < 0x7f then { a with osize := a.osize + 1 }
  else if isPrintable ch then { a with maxch := max ch a.maxch, osize := a.osize + 1 }
  else if ch < 0x100 then { a with osize := a.osize + 4 }
  else if ch < 0x10000 then { a with osize := a.osize + 6 }
  else { a with osize := a.osize + 10 }

def reprScan (s : Str) : ReprScan := s.foldl reprScanStep {}

/-- The quote chosen at unicodeobject.c:12751-12761. -/
def reprQuote (squote dquote : Nat) : Nat :=
  if squote ≠ 0 ∧ dquote = 0 then 34 else 39

/-- The output for one character, stringlib/repr.h:18-90. -/
def reprChar (quote ch : Nat) : Str :=
  if ch = quote ∨ ch = 92 then [92, ch]
  else if ch = 9 then [92, 116]
  else if ch = 10 then [92, 110]
  else if ch = 13 then [92, 114]
  else if ch < 32 ∨ ch = 0x7F then [92, 120] ++ hexDigits 2 ch
  else if ch < 0x7F then [ch]
  else if !isPrintable ch then
    if ch ≤ 0xff then [92, 120] ++ hexDigits 2 ch
    else if ch ≤ 0xffff then [92, 117] ++ hexDigits 4 ch
    else [92, 85] ++ hexDigits 8 ch
  else [ch]

/-- `STRINGLIB(repr)`, stringlib/repr.h:8-95. -/
def stringlibRepr (s : Str) (quote : Nat) : Str :=
  [quote] ++ s.flatMap (reprChar quote) ++ [quote]

/-- `unicode_repr`, unicodeobject.c:12707-12795. Returns the result together with
the `osize` and `maxch` the first pass computed, which the C code uses to allocate
the output. The `OverflowError` branch needs an input of about `PY_SSIZE_T_MAX / 10`
characters, which no allocation can provide. -/
def reprFinish (s : Str) (a : ReprScan) : Str × Nat × Nat :=
  let quote := reprQuote a.squote a.dquote
  let changed := a.osize != s.length || a.squote != 0
  let osize := (if a.squote ≠ 0 ∧ a.dquote ≠ 0 then a.osize + a.squote else a.osize) + 2
  let out := if !changed then [quote] ++ s ++ [quote] else stringlibRepr s quote
  (out, osize, a.maxch)

def unicodeReprFull (s : Str) : Str × Nat × Nat := reprFinish s (reprScan s)

/-- `repr(s)`. -/
def unicodeRepr (s : Str) : Str := (unicodeReprFull s).1

example : unicodeRepr (lit "a'b") = lit "\"a'b\"" := by decide
example : unicodeRepr [0xD800] = lit "'\\ud800'" := by decide

end PyLean.UnicodeObj
