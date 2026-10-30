import PyLean.Decimal.Basic

/-!
`Decimal(str)` in both twins.

**`_pydecimal`** (_pydecimal.py:486-532): `_parser(value.strip().replace("_", ""))`
with the regex at :6100-6118, compiled with `re.VERBOSE | re.IGNORECASE`:

```
(?P<sign>[-+])?
(  (?=\d|\.\d) (?P<int>\d*) (\.(?P<frac>\d*))? (E(?P<exp>[-+]?\d+))?
 | Inf(inity)?
 | (?P<signal>s)? NaN (?P<diag>\d*) )
\z
```

`pyMatch` follows the regex's backtracking to its unique outcome: the three
alternatives start with disjoint characters (a digit or `.`, an `i`, an `s`
or `n`), and every greedy `\d*` is followed by a piece that cannot start
with a digit. `\d` is Unicode `Nd`. Under `IGNORECASE`, a pattern letter
matches its two ASCII cases and, by Unicode simple case folding, also
`İ` (U+0130) and `ı` (U+0131) for `i` and `ſ` (U+017F) for `s`; no other
non-ASCII character matches a letter of this pattern (checked exhaustively
against `re` on 3.14.7). The groups then go through `int()`, which applies
the 4300-digit limit.

**`_decimal`** (_decimal.c:2276-2293 → 2222-2250): `numeric_as_ascii(u, 1, 1)`
(:2143-2195) strips Unicode whitespace, drops `_`, keeps ASCII, maps other
whitespace to `' '` and `Nd` digits to ASCII, and rejects anything else; then
`mpd_qset_string` (libmpdec/io.c:200-328) under `mpd_maxcontext`, and any
Inexact/Rounded/Clamped becomes InvalidOperation (:2240-2244).
-/

namespace PyLean.Decimal

open PyLean

/-! ## The Python twin -/

/-- Does `c` match the pattern letter `p` (lowercase ASCII) under `re.IGNORECASE`? -/
def ciMatch (p : Char) (c : Char) : Bool :=
  c == p || c == p.toUpper ||
  (p == 'i' && (c.toNat == 0x130 || c.toNat == 0x131)) ||
  (p == 's' && c.toNat == 0x17F)

/-- Match the literal word `w` (lowercase) at the start of `s`; return the rest. -/
def matchWord : List Char → List Char → Option (List Char)
  | [], s => some s
  | _ :: _, [] => none
  | p :: ps, c :: cs => if ciMatch p c then matchWord ps cs else none

/-- The outcome of the regex: which alternative matched, with its groups. -/
inductive PyMatch where
  /-- `sign`, `int`, `frac` (`None` and `''` both read as `''` by the
  caller), and `exp` (its optional sign and its digits). -/
  | num (neg : Bool) (intpart : List Char) (frac : List Char) (exp : Option (Bool × List Char))
  | inf (neg : Bool)
  | nan (neg : Bool) (signal : Bool) (diag : List Char)
  deriving Repr, DecidableEq

/-- `(E(?P<exp>[-+]?\d+))? \z` on what follows the fraction. -/
def matchExpEnd : List Char → Option (Option (Bool × List Char))
  | [] => some none
  | c :: cs =>
    if c == 'e' || c == 'E' then
      let (eneg, body) := match cs with
        | '-' :: r => (true, r)
        | '+' :: r => (false, r)
        | r => (false, r)
      if body ≠ [] ∧ body.all isDigit then some (some (eneg, body)) else none
    else none

/-- The numeric alternative after the lookahead. -/
def matchNum (neg : Bool) (s : List Char) : Option PyMatch :=
  let intpart := s.takeWhile isDigit
  let r1 := s.dropWhile isDigit
  let (frac, r2) := match r1 with
    | '.' :: r => (r.takeWhile isDigit, r.dropWhile isDigit)
    | r => ([], r)
  match matchExpEnd r2 with
  | some ex => some (.num neg intpart frac ex)
  | none => none

/-- `_parser(t)` (`re.match` with `\z`), returning the groups. -/
def pyMatch (t : List Char) : Option PyMatch :=
  let (neg, s) := match t with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  -- (?=\d|\.\d)
  let look := match s with
    | c :: r => isDigit c || (c == '.' && match r with | d :: _ => isDigit d | [] => false)
    | [] => false
  if look then matchNum neg s
  else match matchWord "inf".toList s with
    | some [] => some (.inf neg)
    | some r => if matchWord "inity".toList r = some [] then some (.inf neg) else none
    | none =>
      let (sig, r) := match s with
        | c :: r => if ciMatch 's' c then (true, r) else (false, c :: r)
        | [] => (false, [])
      match matchWord "nan".toList r with
      | some d => if d.all isDigit then some (.nan neg sig d) else none
      | none => none

/-- `_pydecimal.Decimal(value)` for a `str` value, _pydecimal.py:486-532,
with the default context (InvalidOperation trapped). -/
def pyParse (s : List Char) : Py Dec :=
  match pyMatch ((strip s).filter (· ≠ '_')) with
  | none => .error invalidOp
  | some (.num neg intpart frac ex) => do
    -- exp = int(m.group('exp') or '0')   (:502)
    let e : Int ← match ex with
      | none => pure 0
      | some (eneg, ds) => do
        intLimit ds.length
        pure (if eneg then -(digitsValue ds : Int) else digitsValue ds)
    -- self._int = str(int(intpart+fracpart))   (:503)
    intLimit (intpart ++ frac).length
    return .fin neg (digitsValue (intpart ++ frac)) (e - frac.length)
  | some (.inf neg) => .ok (.inf neg)
  | some (.nan neg sig d) => do
    -- self._int = str(int(diag or '0')).lstrip('0')   (:510)
    intLimit (if d = [] then 1 else d.length)
    return .nan neg sig (digitsValue d)

/-! ## The C twin -/

/-- `numeric_as_ascii(u, strip_ws=1, ignore_underscores=1)`, _decimal.c:2143-2195.
An invalid character makes the whole result the empty string. -/
def numericAsAscii (s : List Char) : List Char :=
  let rec go : List Char → Option (List Char)
    | [] => some []
    | c :: cs =>
      if c == '_' then go cs
      else if 0 < c.toNat ∧ c.toNat ≤ 127 then (c :: ·) <$> go cs
      else if isSpace c then (' ' :: ·) <$> go cs
      else match digitVal c with
        | some d => (Char.ofNat (48 + d) :: ·) <$> go cs
        | none => none
  (go (strip s)).getD []

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `_mpd_strneq(s, l, u, n)` (io.c:63-74) comparing the next `n = len(l)`
characters; with `nul = true` the terminating NUL is compared too
(`n = strlen(l)+1`), i.e. the rest must be exactly the word. -/
def strneq (w : List Char) (s : List Char) (nul : Bool) : Option (List Char) :=
  match w, s with
  | [], r => if nul then (if r = [] then some [] else none) else some r
  | _ :: _, [] => none
  | p :: ps, c :: cs => if c == p || c == p.toUpper then strneq ps cs nul else none

/-- `scan_payload` (io.c:183-196): skip zeros, then digits to the end. Returns
the significant payload digits. -/
def scanPayload (s : List Char) : Option (List Char) :=
  let r := s.dropWhile (· == '0')
  if r.all isAsciiDigit then some r else none

/-- The state of `scan_dpoint_exp` (io.c:137-179) after a prefix: the
indices of the decimal point, of the indicator and of the first relevant
coefficient digit. `afterE` records that the previous character was the
indicator, so that a following sign is skipped (io.c:155-156). -/
structure ScanState where
  dpoint : Option Nat := none
  exp : Option Nat := none
  coeff : Option Nat := none
  afterE : Bool := false
  deriving Repr

/-- `scan_dpoint_exp`: the loop over the characters at positions `i`,
`i+1`, ...; `none` for a syntax error. -/
def scanLoop : Nat → List Char → ScanState → Option ScanState
  | _, [], st => some st
  | i, c :: cs, st =>
    if st.afterE && (c == '+' || c == '-') then scanLoop (i + 1) cs { st with afterE := false }
    else
    let st := { st with afterE := false }
    if c == '.' then
      if st.dpoint.isSome || st.exp.isSome then none
      else scanLoop (i + 1) cs { st with dpoint := some i }
    else if c == 'E' || c == 'e' then
      if st.exp.isSome then none
      else scanLoop (i + 1) cs { st with exp := some i, afterE := true }
    else if !isAsciiDigit c then none
    else if st.coeff.isNone && st.exp.isNone then
      if c == '0' then
        let next := cs.head?
        let next2 := (cs.drop 1).head?
        let nextDigit := match next with | some d => isAsciiDigit d | none => false
        let dotDigit := next == some '.' && (match next2 with | some d => isAsciiDigit d | none => false)
        if !nextDigit && !dotDigit then scanLoop (i + 1) cs { st with coeff := some i }
        else scanLoop (i + 1) cs st
      else scanLoop (i + 1) cs { st with coeff := some i }
    else scanLoop (i + 1) cs st

/-- `mpd_strtossize` (= `strtoll`) on the indicator's tail, as used by
`strtoexp` (io.c:76-88) and the `errno` test at io.c:273-278: `none` for
`EINVAL`, a saturated value on `ERANGE`. The tail is `[+-]?digits` by the
scan. -/
def strtoexp (t : List Char) : Option Int :=
  let (neg, body) := match t with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if body = [] then none
  else
    let v : Int := if neg then -(digitsValue body : Int) else digitsValue body
    some (max mpdSsizeMin (min mpdSsizeMax v))

/-- Result of `mpd_qset_string` before the exactness check. -/
inductive MpdParse where
  | syntax
  | fin (neg : Bool) (coeff : Nat) (digits : Nat) (exp : Int)
  | inf (neg : Bool)
  | nan (neg : Bool) (signaling : Bool) (payload : Nat) (digits : Nat)
  deriving Repr, DecidableEq

/-- `mpd_qset_string(dec, s, maxcontext)`, io.c:200-328, up to the call of
`mpd_qfinalize`. -/
def mpdSetString (s0 : List Char) : MpdParse :=
  let (neg, s) := match s0 with
    | '+' :: r => (false, r)
    | '-' :: r => (true, r)
    | r => (false, r)
  let payload (sig : Bool) (r : List Char) : MpdParse :=
    if r = [] then .nan neg sig 0 0
    else match scanPayload r with
      | none => .syntax
      | some ds => if (ds.length : Int) > mpdMaxPrec then .syntax
                   else .nan neg sig (digitsValue ds) ds.length
  match strneq "nan".toList s false with
  | some r => payload false r
  | none =>
  match strneq "snan".toList s false with
  | some r => payload true r
  | none =>
  match strneq "inf".toList s false with
  | some r => if r = [] || (strneq "inity".toList r true).isSome then .inf neg else .syntax
  | none =>
  match scanLoop 0 s {} with
  | none => .syntax
  | some st =>
    match st.coeff with
    | none => .syntax
    | some coeff =>
      let fin := s.length
      -- exponent-part (io.c:269-279)
      let ex : Option (Option Int) := match st.exp with
        | none => some none
        | some x => (some <$> strtoexp (s.drop (x + 1)))
      match ex with
      | none => .syntax
      | some ex =>
        let e0 : Int := ex.getD 0
        let endc := st.exp.getD fin
        let digits0 := endc - coeff
        let (digits, fracdigits) := match st.dpoint with
          | some d => (if d > coeff then digits0 - 1 else digits0, some (endc - d - 1))
          | none => (digits0, none)
        let fracOk := match fracdigits with | some f => (f : Int) ≤ mpdMaxPrec | none => true
        if !fracOk then .syntax else
        let e1 : Int := match fracdigits with
          | some f => if e0 < mpdSsizeMin + f then mpdSsizeMin else e0 - f
          | none => e0
        if (digits : Int) > mpdMaxPrec then .syntax else
        let e2 := if e1 > mpdExpInf then mpdExpInf else e1
        let e3 := if e2 = mpdSsizeMin then mpdSsizeMin + 1 else e2
        -- string_to_coeff: the `digits` digits from `coeff`, skipping the point
        let cds := ((s.drop coeff).take (endc - coeff)).filter (· != '.')
        .fin neg (digitsValue cds) digits e3

/-- `PyDecType_FromUnicodeExactWS` (_decimal.c:2276-2293 and 2222-2250), with
the default context (InvalidOperation trapped). -/
def cParse (s : List Char) : Py Dec :=
  match mpdSetString (numericAsAscii s) with
  | .syntax => .error invalidOp
  | .inf neg => .ok (.inf neg)
  | .nan neg sig p _ => .ok (.nan neg sig p)
  | .fin neg c _ e =>
    -- mpd_qfinalize under maxcontext; Inexact/Rounded/Clamped → InvalidOperation
    if InCLimits (.fin neg c e) then .ok (.fin neg c e) else .error invalidOp

end PyLean.Decimal
