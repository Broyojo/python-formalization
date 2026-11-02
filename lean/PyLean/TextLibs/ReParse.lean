import PyLean.Core

/-!
Model of `Lib/re/_parser.py` and `PatternError` in `Lib/re/_constants.py`, CPython 3.15.2.

Not modelled: `\N{...}`, which needs the Unicode name database, and non-ASCII group names, whose
`str.isidentifier` needs XID tables. The difftest generates neither. `FutureWarning`s and
`SRE_FLAG_DEBUG`'s dump are not part of a parse result.
-/

namespace PyLean.TextLibs.Re

open PyLean

def MAXREPEAT : Nat := 4294967295
def MAXGROUPS : Nat := 2147483647
def MAXWIDTH : Nat := 2 ^ 64

def FLAG_IGNORECASE : Nat := 2
def FLAG_LOCALE : Nat := 4
def FLAG_MULTILINE : Nat := 8
def FLAG_DOTALL : Nat := 16
def FLAG_UNICODE : Nat := 32
def FLAG_VERBOSE : Nat := 64
def FLAG_DEBUG : Nat := 128
def FLAG_ASCII : Nat := 256
def TYPE_FLAGS : Nat := FLAG_ASCII ||| FLAG_LOCALE ||| FLAG_UNICODE
def GLOBAL_FLAGS : Nat := FLAG_DEBUG

inductive AtCode where
  | beginning | beginningString | boundary | nonBoundary | end_ | endString
  deriving Repr, DecidableEq, Inhabited

inductive Cat where
  | digit | notDigit | space | notSpace | word | notWord
  deriving Repr, DecidableEq, Inhabited

inductive SetItem where
  | literal (c : Nat)
  | range (lo hi : Nat)
  | category (c : Cat)
  | negate
  deriving Repr, DecidableEq, Inhabited

inductive RepeatKind where
  | max | min | possessive
  deriving Repr, DecidableEq, Inhabited

/-- One `(op, av)` of a `SubPattern`. -/
inductive Node where
  | literal (c : Nat)
  | notLiteral (c : Nat)
  | any
  | in_ (set : List SetItem)
  | at_ (a : AtCode)
  | groupref (g : Nat)
  | grouprefExists (g : Nat) (yes : List Node) (no : Option (List Node))
  | branch (alts : List (List Node))
  | subpattern (group : Option Nat) (add del : Nat) (p : List Node)
  | repeat_ (k : RepeatKind) (lo hi : Nat) (p : List Node)
  | atomic (p : List Node)
  | assert_ (dir : Int) (p : List Node)
  | assertNot (dir : Int) (p : List Node)
  | failure
  deriving Repr, Inhabited

/-- Python's `==` on two `(op, av)` tuples, as `_parse_sub` uses it. A `SubPattern` has no
`__eq__`, so any two tuples that hold one compare by identity, and are different objects. -/
def atomEq : Node → Node → Bool
  | .literal a, .literal b | .notLiteral a, .notLiteral b | .groupref a, .groupref b => a == b
  | .any, .any | .failure, .failure => true
  | .in_ a, .in_ b => a == b
  | .at_ a, .at_ b => a == b
  | _, _ => false

/-- The final `min(lo, MAXWIDTH), min(hi, MAXWIDTH)`. -/
def clampW (w : Nat × Nat) : Nat × Nat := (Nat.min w.1 MAXWIDTH, Nat.min w.2 MAXWIDTH)

mutual
  /-- `SubPattern.getwidth`, `Lib/re/_parser.py:178-228`. `gw` is `state.groupwidths`. -/
  def widthList (gw : List (Option (Nat × Nat))) : List Node → Nat × Nat
    | [] => (0, 0)
    | n :: ns =>
      let (lo, hi) := widthNode gw n (widthList gw ns).1 (widthList gw ns).2
      (lo, hi)

  /-- The contribution of one item, added to the `lo`, `hi` of the items after it. Addition is
  commutative, except that a repeat with `MAXREPEAT` sets `hi` outright; `getwidth` clamps
  that with `min(hi, MAXWIDTH)` at the end, so `hi` only needs to stay above it. -/
  def widthNode (gw : List (Option (Nat × Nat))) : Node → Nat → Nat → Nat × Nat
    | .branch alts, lo, hi =>
      let (i, j) := widthAlts gw alts
      (lo + i, hi + j)
    | .atomic p, lo, hi =>
      let (i, j) := clampW (widthList gw p)
      (lo + i, hi + j)
    | .subpattern _ _ _ p, lo, hi =>
      let (i, j) := clampW (widthList gw p)
      (lo + i, hi + j)
    | .repeat_ _ mn mx p, lo, hi =>
      let (i, j) := clampW (widthList gw p)
      (lo + i * mn, if mx = MAXREPEAT ∧ j ≠ 0 then hi + MAXWIDTH else hi + j * mx)
    | .literal _, lo, hi | .notLiteral _, lo, hi | .any, lo, hi | .in_ _, lo, hi =>
      (lo + 1, hi + 1)
    | .groupref g, lo, hi =>
      let (i, j) := ((gw.getD g none).getD (0, 0))
      (lo + i, hi + j)
    | .grouprefExists _ yes no, lo, hi =>
      let (i, j) := clampW (widthList gw yes)
      match no with
      | some n =>
        let (l, h) := clampW (widthList gw n)
        (lo + Nat.min i l, hi + Nat.max j h)
      | none => (lo, hi + j)
    | _, lo, hi => (lo, hi)

  def widthAlts (gw : List (Option (Nat × Nat))) : List (List Node) → Nat × Nat
    | [] => (MAXWIDTH, 0)
    | a :: as =>
      let (l, h) := clampW (widthList gw a)
      let (i, j) := widthAlts gw as
      (Nat.min i l, Nat.max j h)
end

def getwidth (gw : List (Option (Nat × Nat))) (p : List Node) : Nat × Nat :=
  clampW (widthList gw p)

/-! ### `PatternError` -/

def textOf (s : List Nat) : String := String.ofList (s.map Char.ofNat)

/-- `PatternError.__init__`, `Lib/re/_constants.py:37-53`; `pattern` and `pos` are present. -/
def patternMessage (msg : String) (pattern : List Nat) (pos : Int) : String :=
  let msg1 := msg ++ s!" at position {pos}"
  let before := pattern.take pos.toNat
  let lineno := (before.filter (· == 10)).length + 1
  let lastNl : Int :=
    match (before.reverse.findIdx? (· == 10)) with
    | some i => (before.length : Int) - 1 - i
    | none => -1
  let colno := pos - lastNl
  if pattern.contains 10 then msg1 ++ s!" (line {lineno}, column {colno})" else msg1

def reError (msg : String) (pattern : List Nat) (pos : Int) : PyExc :=
  .named "PatternError" (patternMessage msg pattern pos)

/-- A message that embeds a `%r`: only its class is compared. -/
def reErrorR (msg : String) : PyExc := .named "PatternError" ("~" ++ msg)

/-! ### Tokenizer -/

/-- `Tokenizer`, `Lib/re/_parser.py:230-310`. `next` is a character, or a backslash and the
character after it. -/
structure Tk where
  istext : Bool
  s : List Nat
  index : Nat
  next : Option (List Nat)
  deriving Repr, Inhabited

/-- `Tokenizer.__next`, `Lib/re/_parser.py:240-255`. -/
def Tk.adv (t : Tk) : Py Tk :=
  match t.s[t.index]? with
  | none => .ok { t with next := none }
  | some 92 =>
    match t.s[t.index + 1]? with
    | none => .error (reError "bad escape (end of pattern)" t.s ((t.s.length : Int) - 1))
    | some c => .ok { t with index := t.index + 2, next := some [92, c] }
  | some c => .ok { t with index := t.index + 1, next := some [c] }

def Tk.tell (t : Tk) : Int := (t.index : Int) - ((t.next.getD []).length : Int)

/-- `msg.encode('ascii', 'backslashreplace')`, the bytes branch of `Tokenizer.error`: only the
class is compared when non-ASCII text would be escaped. -/
def Tk.err (t : Tk) (msg : String) (offset : Int := 0) : PyExc :=
  if !t.istext ∧ msg.toList.any (fun c => decide (c.toNat ≥ 128)) then reErrorR msg
  else reError msg t.s (t.tell - offset)

/-- `Tokenizer.seek`, `Lib/re/_parser.py:295-297`. -/
def Tk.seek (t : Tk) (i : Int) : Py Tk := Tk.adv { t with index := i.toNat }

/-- The parser's mutable state: the `Tokenizer` and `State`, `Lib/re/_parser.py:75-109`. -/
structure PSt where
  tk : Tk
  flags : Nat
  groupdict : List (List Nat × Nat) := []
  groupwidths : List (Option (Nat × Nat)) := [none]
  lookbehindgroups : Option Nat := none
  grouprefpos : List (Nat × Int) := []
  /-- `sys.get_int_max_str_digits()`: 4300 by default, and at least 640 when set. -/
  maxDigits : Nat := 4300
  deriving Repr, Inhabited

abbrev P := StateT PSt (Except PyExc)

def pErr {α : Type} (msg : String) (offset : Int := 0) : P α := do
  throw ((← get).tk.err msg offset)

def tell : P Int := do return (← get).tk.tell
def peek : P (Option (List Nat)) := do return (← get).tk.next

/-- `State.opengroup`, `Lib/re/_parser.py:86-97`. The two errors are re-raised by the `except` in
`_parse` with the offset `len(name) + 1`, `Lib/re/_parser.py:849-850`. That `len(name)` would be a
`TypeError` for an unnamed group, which needs `MAXGROUPS` groups and is out of the model's reach. -/
def opengroupPure (st : PSt) (name : Option (List Nat)) : Py (Nat × PSt) :=
  let gid := st.groupwidths.length
  let st' := { st with groupwidths := st.groupwidths ++ [none] }
  if st'.groupwidths.length > MAXGROUPS then
    .error (st.tk.err "too many groups" ((name.getD []).length + 1))
  else
    match name with
    | none => .ok (gid, st')
    | some n =>
      if (st.groupdict.lookup n).isSome then .error (reErrorR "redefinition of group name")
      else .ok (gid, { st' with groupdict := st.groupdict ++ [(n, gid)] })

/-- `State.closegroup`, `Lib/re/_parser.py:98-99`. `width` is `p.getwidth()`. -/
def closegroupPure (st : PSt) (gid : Nat) (width : Nat × Nat) : PSt :=
  { st with groupwidths := st.groupwidths.set gid (some width) }

/-- `Tokenizer.get`. -/
def sget : P (Option (List Nat)) := do
  let st ← get
  let t ← liftM (m := Except PyExc) st.tk.adv
  set { st with tk := t }
  return st.tk.next

/-- `Tokenizer.match`. -/
def smatch (c : Nat) : P Bool := do
  if (← peek) == some [c] then
    let _ ← sget
    return true
  return false

def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isOct (c : Nat) : Bool := 48 ≤ c && c ≤ 55
def isHex (c : Nat) : Bool := isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)
def isLetter (c : Nat) : Bool := (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90)

/-- `Tokenizer.getwhile`, `Lib/re/_parser.py:265-273`. -/
def getwhile : Nat → (Nat → Bool) → P (List Nat)
  | 0, _ => pure []
  | n + 1, set => do
    match ← peek with
    | some [c] =>
      if set c then
        let _ ← sget
        return c :: (← getwhile n set)
      else return []
    | _ => return []

/-- `Tokenizer.getuntil`, `Lib/re/_parser.py:274-289`. `result` is the `str` so far, in which a
two-character token counts twice. -/
def getuntil (terminator : Nat) (name : String) : (fuel : Nat) → (result : List Nat) → P (List Nat)
  | 0, _ => throw .modelFuel
  | fuel + 1, result => do
    let c ← sget
    match c with
    | none =>
      if result.isEmpty then pErr ("missing " ++ name)
      else pErr s!"missing {String.singleton (Char.ofNat terminator)}, unterminated name" result.length
    | some t =>
      if t == [terminator] then
        if result.isEmpty then pErr ("missing " ++ name) 1
        else return result
      else getuntil terminator name fuel (result ++ t)

/-- `str.isidentifier` on ASCII names. -/
def isIdentifier (s : List Nat) : Bool :=
  match s with
  | [] => false
  | c :: r =>
    (isLetter c || c == 95) && r.all (fun x => isLetter x || isDigit x || x == 95)

/-- `Tokenizer.checkgroupname`, `Lib/re/_parser.py:304-310`. -/
def checkgroupname (name : List Nat) : P Unit := do
  if !isIdentifier name then
    throw (reErrorR "bad character in group name")

/-- `int(s, base)` on digits already checked. -/
def intOf (base : Nat) (s : List Nat) : Nat :=
  s.foldl (fun x c =>
    x * base + (if isDigit c then c - 48 else if 97 ≤ c then c - 87 else c - 55)) 0

/-- `int(s)` for a decimal string: past `sys.get_int_max_str_digits()` digits it raises
`ValueError`. -/
def intDec (lim : Nat) (s : List Nat) : Py Nat :=
  if s.length > lim then
    .error (.valueError s!"Exceeds the limit ({lim} digits) for integer string conversion: value has {s.length} digits; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (intOf 10 s)

def liftPy {α : Type} (r : Py α) : P α := liftM (m := Except PyExc) r

/-- `ESCAPES`, `Lib/re/_parser.py:31-40`. -/
def escapesGet (c : Nat) : Option Nat :=
  match c with
  | 97 => some 7 | 98 => some 8 | 102 => some 12 | 110 => some 10
  | 114 => some 13 | 116 => some 9 | 118 => some 11 | 92 => some 92
  | _ => none

/-- `CATEGORIES`, `Lib/re/_parser.py:42-54`. -/
def categoriesGet (c : Nat) : Option Node :=
  match c with
  | 65 => some (.at_ .beginningString)
  | 98 => some (.at_ .boundary)
  | 66 => some (.at_ .nonBoundary)
  | 100 => some (.in_ [.category .digit])
  | 68 => some (.in_ [.category .notDigit])
  | 115 => some (.in_ [.category .space])
  | 83 => some (.in_ [.category .notSpace])
  | 119 => some (.in_ [.category .word])
  | 87 => some (.in_ [.category .notWord])
  | 122 => some (.at_ .endString)
  | 90 => some (.at_ .endString)
  | _ => none

/-- The `\x`, `\u` and `\U` escapes shared by `_class_escape` and `_escape`: the escape as
extended by `getwhile`, and its value. -/
def hexEscape (escape : List Nat) (n : Nat) : P (List Nat × Nat) := do
  let more ← getwhile n isHex
  let e := escape ++ more
  if e.length ≠ n + 2 then pErr ("incomplete escape " ++ textOf e) e.length
  return (e, intOf 16 more)

/-- The tail of both escape functions, `Lib/re/_parser.py:364-370`, `:441-447`. -/
def plainEscape (escape : List Nat) : P Node := do
  match escape with
  | [_, c] =>
    if isLetter c then pErr ("bad escape " ++ textOf escape) 2
    else return .literal c
  | _ => pErr ("bad escape " ++ textOf escape) escape.length

/-- `_class_escape`, `Lib/re/_parser.py:312-370`. -/
def classEscape (escape : List Nat) : P Node := do
  let c := escape.getD 1 0
  if let some v := escapesGet c then return .literal v
  if let some n := categoriesGet c then
    match n with
    | .in_ _ => return n
    | _ => pure ()
  let istext := (← get).tk.istext
  if c = 120 then
    return .literal (← hexEscape escape 2).2
  else if c = 117 ∧ istext then
    return .literal (← hexEscape escape 4).2
  else if c = 85 ∧ istext then
    let (e, v) ← hexEscape escape 8
    if v > 0x10FFFF then pErr ("bad escape " ++ textOf e) e.length
    return .literal v
  else if isOct c then
    let more ← getwhile 2 isOct
    let e := escape ++ more
    let v := intOf 8 (c :: more)
    if v > 255 then
      pErr s!"octal escape value {textOf e} outside of range 0-0o377" e.length
    return .literal v
  else if isDigit c then
    pErr ("bad escape " ++ textOf escape) escape.length
  else plainEscape escape

/-- `State.checkgroup`, `Lib/re/_parser.py:100-101`. -/
def checkgroup (st : PSt) (gid : Nat) : Bool :=
  gid < st.groupwidths.length && (st.groupwidths.getD gid none).isSome

/-- `State.checklookbehindgroup`, `Lib/re/_parser.py:103-109`: the message, if it raises. -/
def lookbehindError (st : PSt) (gid : Nat) : Option String :=
  match st.lookbehindgroups with
  | none => none
  | some lb =>
    if !checkgroup st gid then some "cannot refer to an open group"
    else if gid ≥ lb then some "cannot refer to group defined in the same lookbehind subpattern"
    else none

def checklookbehindgroup (gid : Nat) : P Unit := do
  if let some m := lookbehindError (← get) gid then pErr m

/-- `_escape`, `Lib/re/_parser.py:372-447`. -/
def escapeCode (escape : List Nat) : P Node := do
  let c := escape.getD 1 0
  if let some n := categoriesGet c then return n
  if let some v := escapesGet c then return .literal v
  let istext := (← get).tk.istext
  if c = 120 then
    return .literal (← hexEscape escape 2).2
  else if c = 117 ∧ istext then
    return .literal (← hexEscape escape 4).2
  else if c = 85 ∧ istext then
    let (e, v) ← hexEscape escape 8
    if v > 0x10FFFF then pErr ("bad escape " ++ textOf e) e.length
    return .literal v
  else if c = 48 then
    let more ← getwhile 2 isOct
    return .literal (intOf 8 (c :: more))
  else if isDigit c then
    -- octal escape *or* decimal group reference
    let (e, oct) ← do
      match ← peek with
      | some [d] =>
        if isDigit d then
          let _ ← sget
          let e := escape ++ [d]
          match ← peek with
          | some [t] =>
            if isOct c && isOct d && isOct t then
              let _ ← sget
              pure (e ++ [t], true)
            else pure (e, false)
          | _ => pure (e, false)
        else pure (escape, false)
      | _ => pure (escape, false)
    if oct then
      let v := intOf 8 (e.drop 1)
      if v > 255 then pErr s!"octal escape value {textOf e} outside of range 0-0o377" e.length
      return .literal v
    let group := intOf 10 (e.drop 1)
    let st ← get
    if group < st.groupwidths.length then
      if !checkgroup st group then pErr "cannot refer to an open group" e.length
      checklookbehindgroup group
      return .groupref group
    pErr s!"invalid group reference {group}" ((e.length : Int) - 1)
  else plainEscape escape

/-! ### `_parse_sub` -/

/-- `_uniq`, `Lib/re/_parser.py:449-450`. -/
def uniq (l : List SetItem) : List SetItem := l.eraseDups

/-- The pfx-factoring loop of `_parse_sub`, `Lib/re/_parser.py:472-488`. -/
def factorPrefix : (fuel : Nat) → List (List Node) → List Node → List (List Node) × List Node
  | 0, items, acc => (items, acc)
  | fuel + 1, items, acc =>
    match items with
    | [] => (items, acc)
    | first :: _ =>
      match first with
      | [] => (items, acc)
      | pfx :: _ =>
        if items.all (fun it => match it with
            | h :: _ => atomEq pfx h
            | [] => false) then
          factorPrefix fuel (items.map (·.drop 1)) (acc ++ [pfx])
        else (items, acc)

/-- The character-set test of `_parse_sub`, `Lib/re/_parser.py:491-501`. -/
def branchSet : List (List Node) → List SetItem → Option (List SetItem)
  | [], acc => some acc
  | [.literal c] :: r, acc => branchSet r (acc ++ [.literal c])
  | [.in_ av] :: r, acc =>
    match av with
    | .negate :: _ => none
    | _ => branchSet r (acc ++ av)
  | _, _ => none

/-- `_parse_sub`'s end, `Lib/re/_parser.py:466-509`. -/
def finishSub (items : List (List Node)) : List Node :=
  match items with
  | [one] => one
  | _ =>
    let (items, sub) := factorPrefix (items.foldl (fun n i => n + i.length) 0 + 1) items []
    match branchSet items [] with
    | some set => sub ++ [.in_ (uniq set)]
    | none => sub ++ [.branch items]

/-- Flag letters, `FLAGS`, `Lib/re/_parser.py:56-66`. -/
def flagOf (c : List Nat) : Option Nat :=
  match c with
  | [105] => some FLAG_IGNORECASE
  | [76] => some FLAG_LOCALE
  | [109] => some FLAG_MULTILINE
  | [115] => some FLAG_DOTALL
  | [120] => some FLAG_VERBOSE
  | [97] => some FLAG_ASCII
  | [117] => some FLAG_UNICODE
  | _ => none

def isAlphaTok (c : List Nat) : Bool :=
  match c with
  | [x] => isLetter x || x ≥ 170
  | _ => false

/-- The first `while True` of `_parse_flags`, `Lib/re/_parser.py:891-912`: returns `add_flags`
and the stopping character. -/
def flagsOn : (fuel : Nat) → List Nat → Nat → P (Nat × List Nat)
  | 0, _, _ => throw .modelFuel
  | fuel + 1, char, add => do
    let flag := (flagOf char).getD 0
    let istext := (← get).tk.istext
    if istext then
      if char == [76] then pErr "bad inline flags: cannot use 'L' flag with a str pattern"
    else
      if char == [117] then pErr "bad inline flags: cannot use 'u' flag with a bytes pattern"
    let add := add ||| flag
    if (flag &&& TYPE_FLAGS) ≠ 0 ∧ (add &&& TYPE_FLAGS) ≠ flag then
      pErr "bad inline flags: flags 'a', 'u' and 'L' are incompatible"
    match ← sget with
    | none => pErr "missing -, : or )"
    | some c =>
      if c == [41] || c == [45] || c == [58] then return (add, c)
      if (flagOf c).isNone then
        pErr (if isAlphaTok c then "unknown flag" else "missing -, : or )") c.length
      flagsOn fuel c add

/-- The second `while True` of `_parse_flags`, `Lib/re/_parser.py:925-938`. -/
def flagsOff : (fuel : Nat) → List Nat → Nat → P Nat
  | 0, _, _ => throw .modelFuel
  | fuel + 1, char, del => do
    let flag := (flagOf char).getD 0
    if (flag &&& TYPE_FLAGS) ≠ 0 then
      pErr "bad inline flags: cannot turn off flags 'a', 'u' and 'L'"
    let del := del ||| flag
    match ← sget with
    | none => pErr "missing :"
    | some c =>
      if c == [58] then return del
      if (flagOf c).isNone then
        pErr (if isAlphaTok c then "unknown flag" else "missing :") c.length
      flagsOff fuel c del

/-- The last checks of `_parse_flags`, `Lib/re/_parser.py:940-944`. -/
def flagsCheck (add del : Nat) : P (Option (Nat × Nat)) :=
  if (del &&& GLOBAL_FLAGS) ≠ 0 then pErr "bad inline flags: cannot turn off global flag" 1
  else if (add &&& del) ≠ 0 then pErr "bad inline flags: flag turned on and off" 1
  else pure (some (add, del))

/-- `_parse_flags`, `Lib/re/_parser.py:886-944`; `none` is the global form `(?x)`. -/
def parseFlags (char : List Nat) : P (Option (Nat × Nat)) := do
  let fuel := (← get).tk.s.length + 8
  let (add, char) ← if char != [45] then flagsOn fuel char 0 else pure (0, char)
  if char == [41] then
    modify fun st => { st with flags := st.flags ||| add }
    return none
  if (add &&& GLOBAL_FLAGS) ≠ 0 then pErr "bad inline flags: cannot turn on global flag" 1
  let del ←
    if char == [45] then
      match ← sget with
      | none => pErr "missing flag"
      | some c =>
        if (flagOf c).isNone then
          pErr (if isAlphaTok c then "unknown flag" else "missing flag") c.length
        flagsOff fuel c 0
    else pure 0
  flagsCheck add del

/-! ### `_parse` -/

def tokIs (t : Option (List Nat)) (c : Nat) : Bool := t == some [c]

def isWhitespace (c : List Nat) : Bool :=
  match c with
  | [x] => x == 32 || x == 9 || x == 10 || x == 13 || x == 11 || x == 12
  | _ => false

/-- `this not in SPECIAL_CHARS`. -/
def isSpecial (c : Nat) : Bool :=
  c == 46 || c == 92 || c == 91 || c == 123 || c == 40 || c == 41 || c == 42 || c == 43 ||
  c == 63 || c == 94 || c == 36 || c == 124

/-- The item a character class code stands for: `code1[1][0]` for an `IN`. -/
def asItem : Node → SetItem
  | .literal c => .literal c
  | .in_ (i :: _) => i
  | _ => .negate

/-- The `while True` of a character set, `Lib/re/_parser.py:564-621`. -/
def setLoop (here : Int) : (fuel : Nat) → List SetItem → P (List SetItem)
  | 0, _ => throw .modelFuel
  | fuel + 1, set => do
    let this? ← sget
    let afterTell ← tell
    match this? with
    | none => pErr "unterminated character set" (afterTell - here)
    | some this =>
      if this == [93] && !set.isEmpty then return set
      let code1 ←
        if this.head? == some 92 then classEscape this
        else pure (Node.literal (this.headD 0))
      if ← smatch 45 then
        match ← sget with
        | none => pErr "unterminated character set" ((← tell) - here)
        | some that =>
          if that == [93] then
            return set ++ [asItem code1, .literal 45]
          let code2 ←
            if that.head? == some 92 then classEscape that
            else pure (Node.literal (that.headD 0))
          match code1, code2 with
          | .literal lo, .literal hi =>
            if hi < lo then
              pErr s!"bad character range {textOf this}-{textOf that}"
                (this.length + 1 + that.length)
            setLoop here fuel (set ++ [.range lo hi])
          | _, _ =>
            pErr s!"bad character range {textOf this}-{textOf that}"
              (this.length + 1 + that.length)
      else setLoop here fuel (set ++ [asItem code1])

/-- The digit runs of `{m,n}`, `Lib/re/_parser.py:655-659`. -/
def digitsRun : (fuel : Nat) → P (List Nat)
  | 0 => pure []
  | fuel + 1 => do
    match ← peek with
    | some [c] =>
      if isDigit c then
        let _ ← sget
        return c :: (← digitsRun fuel)
      return []
    | _ => return []

/-- `subpattern[i: i+1] = p` for plain non-capturing groups, `Lib/re/_parser.py:877-882`. -/
def unpackGroups (sub : List Node) : List Node :=
  sub.flatMap fun n =>
    match n with
    | .subpattern none 0 0 p => p
    | _ => [n]

mutual
  /-- `_parse_sub`, `Lib/re/_parser.py:452-509`. `verbose` is the truth of the argument. -/
  def parseSub : (fuel : Nat) → Bool → Nat → P (List Node)
    | 0, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested => do
      let items ← parseAlts fuel verbose nested []
      return finishSub items

  def parseAlts : (fuel : Nat) → Bool → Nat → List (List Node) → P (List (List Node))
    | 0, _, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested, items => do
      let it ← parseSeq fuel verbose (nested + 1) (nested == 0 && items.isEmpty) []
      let items := items ++ [it]
      if ← smatch 124 then
        let verbose ←
          if nested == 0 then pure (decide (((← get).flags &&& FLAG_VERBOSE) ≠ 0)) else pure verbose
        parseAlts fuel verbose nested items
      else return items

  /-- The `while True` of `_parse`, `Lib/re/_parser.py:522-874`, then the unpacking of
  non-capturing groups, `:877-882`. `sub` is the `subpattern` so far. -/
  def parseSeq : (fuel : Nat) → Bool → Nat → Bool → List Node → P (List Node)
    | 0, _, _, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested, first, sub => do
      let this? ← peek
      match this? with
      | none => return unpackGroups sub
      | some this =>
        if this == [124] || this == [41] then return unpackGroups sub
        let _ ← sget
        if verbose && isWhitespace this then
          return ← parseSeq fuel verbose nested first sub
        if verbose && this == [35] then
          skipComment fuel
          return ← parseSeq fuel verbose nested first sub
        if this.head? == some 92 then
          let code ← escapeCode this
          return ← parseSeq fuel verbose nested first (sub ++ [code])
        let c := this.headD 0
        if !isSpecial c then
          return ← parseSeq fuel verbose nested first (sub ++ [.literal c])
        if c == 91 then
          let here := (← tell) - 1
          let negate ← smatch 94
          let set ← setLoop here fuel []
          let set := uniq set
          let code : Node :=
            match set with
            | [.literal v] => if negate then .notLiteral v else .literal v
            | _ => .in_ (if negate then .negate :: set else set)
          return ← parseSeq fuel verbose nested first (sub ++ [code])
        if c == 42 || c == 43 || c == 63 || c == 123 then
          return ← parseRepeat fuel verbose nested first sub c
        if c == 46 then return ← parseSeq fuel verbose nested first (sub ++ [.any])
        if c == 40 then return ← parseGroup fuel verbose nested first sub
        if c == 94 then
          return ← parseSeq fuel verbose nested first (sub ++ [.at_ .beginning])
        if c == 36 then
          return ← parseSeq fuel verbose nested first (sub ++ [.at_ .end_])
        throw (.assertionError "~unsupported special character")

  /-- The `while True` of a verbose comment, `Lib/re/_parser.py:536-539`. -/
  def skipComment : (fuel : Nat) → P Unit
    | 0 => throw .modelFuel
    | fuel + 1 => do
      match ← sget with
      | none => return ()
      | some t => if t == [10] then return () else skipComment fuel

  /-- The quantifier branch, `Lib/re/_parser.py:638-703`. -/
  def parseRepeat : (fuel : Nat) → Bool → Nat → Bool → List Node → Nat → P (List Node)
    | 0, _, _, _, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested, first, sub, c => do
      let here ← tell
      let bounds ← (do
        if c == 63 then pure (some (0, 1))
        else if c == 42 then pure (some (0, MAXREPEAT))
        else if c == 43 then pure (some (1, MAXREPEAT))
        else
          if tokIs (← peek) 125 then pure none
          else
            let n := (← get).tk.s.length + 1
            let lo ← digitsRun n
            let comma ← smatch 44
            let hi ← if comma then digitsRun n else pure lo
            if !(← smatch 125) then
              let st ← get
              let t ← liftPy (st.tk.seek here)
              set { st with tk := t }
              pure none
            else
              let mn ←
                if lo.isEmpty then pure 0
                else
                  let v ← liftPy (intDec (← get).maxDigits lo)
                  if v ≥ MAXREPEAT then
                    throw (.overflowError "the repetition number is too large")
                  pure v
              let mx ←
                if hi.isEmpty then pure MAXREPEAT
                else
                  let v ← liftPy (intDec (← get).maxDigits hi)
                  if v ≥ MAXREPEAT then
                    throw (.overflowError "the repetition number is too large")
                  if v < mn then
                    pErr "min repeat greater than max repeat" ((← tell) - here)
                  pure v
              pure (some (mn, mx)))
      match bounds with
      | none => parseSeq fuel verbose nested first (sub ++ [.literal 123])
      | some (mn, mx) =>
        let t ← tell
        let last := sub.getLast?
        match last with
        | none | some (.at_ _) => pErr "nothing to repeat" (t - here + 1)
        | some (.repeat_ _ _ _ _) => pErr "multiple repeat" (t - here + 1)
        | some n =>
          let item : List Node :=
            match n with
            | .subpattern none 0 0 p => p
            | _ => [n]
          let kind ← (do
            if ← smatch 63 then pure RepeatKind.min
            else if ← smatch 43 then pure RepeatKind.possessive
            else pure RepeatKind.max)
          parseSeq fuel verbose nested first (sub.dropLast ++ [.repeat_ kind mn mx item])

  /-- The `(` branch, `Lib/re/_parser.py:708-865`. -/
  def parseGroup : (fuel : Nat) → Bool → Nat → Bool → List Node → P (List Node)
    | 0, _, _, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested, first, sub => do
      let start := (← tell) - 1
      let cont (n : List Node) := parseSeq fuel verbose nested first n
      if !(← smatch 63) then
        return ← finishGroup fuel verbose nested first sub start true false none 0 0
      match ← sget with
      | none => pErr "unexpected end of pattern"
      | some char =>
        if char == [80] then
          if ← smatch 60 then
            let name ← getuntil 62 "group name" (fuel + 1) []
            checkgroupname name
            return ← finishGroup fuel verbose nested first sub start true false (some name) 0 0
          if ← smatch 61 then
            let name ← getuntil 41 "group name" (fuel + 1) []
            checkgroupname name
            let st ← get
            match st.groupdict.lookup name with
            | none => throw (reErrorR "unknown group name")
            | some gid =>
              if !checkgroup st gid then pErr "cannot refer to an open group" (name.length + 1)
              checklookbehindgroup gid
              return ← cont (sub ++ [.groupref gid])
          match ← sget with
          | none => pErr "unexpected end of pattern"
          | some c => pErr ("unknown extension ?P" ++ textOf c) (c.length + 2)
        if char == [58] then
          return ← finishGroup fuel verbose nested first sub start false false none 0 0
        if char == [35] then
          skipParenComment fuel start
          return ← cont sub
        if char == [61] || char == [33] || char == [60] then
          let (char, dir, saved) ← (do
            if char == [60] then
              match ← sget with
              | none => pErr "unexpected end of pattern"
              | some c =>
                if !(c == [61] || c == [33]) then
                  pErr ("unknown extension ?<" ++ textOf c) (c.length + 2)
                let st ← get
                let lb := st.lookbehindgroups
                if lb.isNone then
                  set { st with lookbehindgroups := some st.groupwidths.length }
                pure (c, (-1 : Int), lb)
            else pure (char, (1 : Int), none))
          let p ← parseSub fuel verbose (nested + 1)
          if dir < 0 ∧ saved.isNone then
            modify fun st => { st with lookbehindgroups := none }
          if !(← smatch 41) then
            pErr "missing ), unterminated subpattern" ((← tell) - start)
          let code : Node :=
            if char == [61] then .assert_ dir p
            else if !p.isEmpty then .assertNot dir p
            else .failure
          return ← cont (sub ++ [code])
        if char == [40] then
          let condname ← getuntil 41 "group name" (fuel + 1) []
          let decimal := !condname.isEmpty && condname.all isDigit
          let condgroup ← (do
            if !decimal then
              checkgroupname condname
              match (← get).groupdict.lookup condname with
              | none => throw (reErrorR "unknown group name")
              | some g => pure g
            else
              let g ← liftPy (intDec (← get).maxDigits condname)
              if g == 0 then pErr "bad group number" (condname.length + 1)
              if g ≥ MAXGROUPS then
                pErr s!"invalid group reference {g}" (condname.length + 1)
              let t ← tell
              modify fun st =>
                if (st.grouprefpos.lookup g).isSome then st
                else { st with grouprefpos := st.grouprefpos ++ [(g, t - condname.length - 1)] }
              pure g)
          checklookbehindgroup condgroup
          let yes ← parseSeq fuel verbose (nested + 1) false []
          let no ← (do
            if ← smatch 124 then
              let n ← parseSeq fuel verbose (nested + 1) false []
              if tokIs (← peek) 124 then
                pErr "conditional backref with more than two branches"
              pure (some n)
            else pure none)
          if !(← smatch 41) then
            pErr "missing ), unterminated subpattern" ((← tell) - start)
          return ← cont (sub ++ [.grouprefExists condgroup yes no])
        if char == [62] then
          return ← finishGroup fuel verbose nested first sub start false true none 0 0
        if (flagOf char).isSome || char == [45] then
          match ← parseFlags char with
          | none =>
            if !first || !sub.isEmpty then
              pErr "global flags not at the start of the expression" ((← tell) - start)
            let v : Bool := decide (((← get).flags &&& FLAG_VERBOSE) ≠ 0)
            return ← parseSeq fuel v nested first sub
          | some (add, del) =>
            return ← finishGroup fuel verbose nested first sub start false false none add del
        pErr ("unknown extension ?" ++ textOf char) (char.length + 1)

  /-- The `(?#...)` comment, `Lib/re/_parser.py:750-758`. -/
  def skipParenComment : (fuel : Nat) → Int → P Unit
    | 0, _ => throw .modelFuel
    | fuel + 1, start => do
      if (← peek).isNone then
        pErr "missing ), unterminated comment" ((← tell) - start)
      match ← sget with
      | some [41] => return ()
      | _ => skipParenComment fuel start

  /-- "parse group contents", `Lib/re/_parser.py:845-865`. -/
  def finishGroup : (fuel : Nat) → Bool → Nat → Bool → List Node → Int → Bool → Bool →
      Option (List Nat) → Nat → Nat → P (List Node)
    | 0, _, _, _, _, _, _, _, _, _, _ => throw .modelFuel
    | fuel + 1, verbose, nested, first, sub, start, capture, atomic, name, add, del => do
      let group ← (do
        if capture then
          let (gid, st') ← liftPy (opengroupPure (← get) name)
          set st'
          pure (some gid)
        else pure none)
      let subVerbose := (verbose || (add &&& FLAG_VERBOSE) ≠ 0) && (del &&& FLAG_VERBOSE) = 0
      let p ← parseSub fuel subVerbose (nested + 1)
      if !(← smatch 41) then
        pErr "missing ), unterminated subpattern" ((← tell) - start)
      if let some g := group then
        modify fun st => closegroupPure st g (getwidth st.groupwidths p)
      let code : Node := if atomic then .atomic p else .subpattern group add del p
      parseSeq fuel verbose nested first (sub ++ [code])

end

/-- `fix_flags`, `Lib/re/_parser.py:946-960`. -/
def fixFlags (istext : Bool) (flags : Nat) : Py Nat :=
  if istext then
    if (flags &&& FLAG_LOCALE) ≠ 0 then .error (.valueError "cannot use LOCALE flag with a str pattern")
    else if (flags &&& FLAG_ASCII) = 0 then .ok (flags ||| FLAG_UNICODE)
    else if (flags &&& FLAG_UNICODE) ≠ 0 then .error (.valueError "ASCII and UNICODE flags are incompatible")
    else .ok flags
  else
    if (flags &&& FLAG_UNICODE) ≠ 0 then .error (.valueError "cannot use UNICODE flag with a bytes pattern")
    else if (flags &&& FLAG_LOCALE) ≠ 0 ∧ (flags &&& FLAG_ASCII) ≠ 0 then
      .error (.valueError "ASCII and LOCALE flags are incompatible")
    else .ok flags

/-- A parsed pattern: the tree and what `compile` needs from `State`. -/
structure Parsed where
  p : List Node
  flags : Nat
  groups : Nat
  groupdict : List (List Nat × Nat)
  groupwidths : List (Option (Nat × Nat))
  deriving Repr, Inhabited

/-- `parse`, `Lib/re/_parser.py:962-987`. -/
def parse (istext : Bool) (s : List Nat) (flags : Nat) (maxDigits : Nat := 4300) : Py Parsed := do
  let t ← Tk.adv ⟨istext, s, 0, none⟩
  let (p, st) ← (parseSub (4 * s.length + 16) ((flags &&& FLAG_VERBOSE) ≠ 0) 0).run { tk := t, flags, maxDigits }
  let fl ← fixFlags istext st.flags
  if st.tk.next.isSome then
    throw (st.tk.err "unbalanced parenthesis")
  for (g, pos) in st.grouprefpos do
    if g ≥ st.groupwidths.length then
      throw (reError s!"invalid group reference {g}" s pos)
  return ⟨p, fl, st.groupwidths.length, st.groupdict, st.groupwidths⟩

/-! ### `parse_template` -/

/-- An item of a compiled replacement. -/
inductive TItem where
  | lit (s : List Nat)
  | group (g : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The state of `parse_template`, `Lib/re/_parser.py:989-1065`. -/
structure TSt where
  tk : Tk
  result : List TItem := []
  literal : List Nat := []
  maxDigits : Nat := 4300
  deriving Repr, Inhabited

abbrev T := StateT TSt (Except PyExc)

def tget : T (Option (List Nat)) := do
  let st ← get
  let t ← liftM (m := Except PyExc) st.tk.adv
  set { st with tk := t }
  return st.tk.next

def tErr {α : Type} (msg : String) (offset : Int := 0) : T α := do
  throw ((← get).tk.err msg offset)

def addLiteral : T Unit :=
  modify fun st => { st with result := st.result ++ [.lit st.literal], literal := [] }

def addGroup (groups : Nat) (index : Nat) (pos : Int) : T Unit := do
  if index > groups then tErr s!"invalid group reference {index}" pos
  addLiteral
  modify fun st => { st with result := st.result ++ [.group index] }

def tpeek : T (Option (List Nat)) := do return (← get).tk.next

def peekOct : T (Option Nat) := do
  match ← tpeek with
  | some [c] => return if isOct c then some c else none
  | _ => return none

def peekDig : T (Option Nat) := do
  match ← tpeek with
  | some [c] => return if isDigit c then some c else none
  | _ => return none

def lappend (s : List Nat) : T Unit :=
  modify fun st => { st with literal := st.literal ++ s }

/-- The `\g<...>` of `parse_template`, `Lib/re/_parser.py:1018-1033`. -/
def templateG (groups : Nat) (groupindex : List (List Nat × Nat)) : T Unit := do
  let st ← get
  if st.tk.next == some [60] then
    let _ ← tget
  else tErr "missing <"
  let rec until_ : (fuel : Nat) → List Nat → T (List Nat)
    | 0, _ => throw .modelFuel
    | fuel + 1, result => do
      match ← tget with
      | none =>
        if result.isEmpty then tErr "missing group name"
        else tErr "missing >, unterminated name" result.length
      | some t =>
        if t == [62] then
          if result.isEmpty then tErr "missing group name" 1
          else return result
        else until_ fuel (result ++ t)
  let name ← until_ (st.tk.s.length + 2) []
  if !(name.all isDigit) then
    if !isIdentifier name then throw (reErrorR "bad character in group name")
    match groupindex.lookup name with
    | some i => addGroup groups i (name.length + 1)
    | none => throw (.indexError "~unknown group name")
  else
    let i ← liftM (m := Except PyExc) (intDec (← get).maxDigits name)
    if i ≥ MAXGROUPS then tErr s!"invalid group reference {i}" (name.length + 1)
    addGroup groups i (name.length + 1)

/-- The loop of `parse_template`, `Lib/re/_parser.py:1011-1063`. -/
def templateLoop (groups : Nat) (groupindex : List (List Nat × Nat)) : (fuel : Nat) → T Unit
  | 0 => throw .modelFuel
  | fuel + 1 => do
    match ← tget with
    | none => return ()
    | some this =>
      match this with
      | [92, c] =>
        if c == 103 then templateG groups groupindex
        else if c == 48 then
          let a ← peekOct
          match a with
          | none => lappend [0]
          | some d =>
            let _ ← tget
            match ← peekOct with
            | some e =>
              let _ ← tget
              lappend [intOf 8 [c, d, e] % 256]
            | none => lappend [intOf 8 [c, d] % 256]
        else if isDigit c then
          match ← peekDig with
          | none => addGroup groups (c - 48) 1
          | some d =>
            let _ ← tget
            let e? ← peekOct
            match e? with
            | some e =>
              if isOct c && isOct d then
                let _ ← tget
                let v := intOf 8 [c, d, e]
                if v > 255 then
                  tErr s!"octal escape value {textOf [92, c, d, e]} outside of range 0-0o377" 4
                lappend [v]
              else addGroup groups (intOf 10 [c, d]) 2
            | none => addGroup groups (intOf 10 [c, d]) 2
        else
          match escapesGet c with
          | some v => lappend [v]
          | none =>
            if isLetter c then tErr ("bad escape " ++ textOf this) this.length
            lappend this
      | _ => lappend this
      templateLoop groups groupindex fuel

/-- `parse_template`, `Lib/re/_parser.py:989-1065`. -/
def parseTemplate (istext : Bool) (s : List Nat) (groups : Nat)
    (groupindex : List (List Nat × Nat)) (maxDigits : Nat := 4300) : Py (List TItem) := do
  let t ← Tk.adv ⟨istext, s, 0, none⟩
  let (_, st) ← (do
    templateLoop groups groupindex (s.length + 2)
    addLiteral).run { tk := t, maxDigits }
  return st.result

end PyLean.TextLibs.Re
