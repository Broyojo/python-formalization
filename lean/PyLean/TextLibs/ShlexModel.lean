import PyLean.Core

/-!
Model of `Lib/shlex.py`, CPython 3.14.7: `read_token`, `__next__`, `split`, `join` and `quote`.

The stream is fallible: `failAt` is the number of calls of `read` and `readline` that succeed before
one raises. `read_token` keeps its attributes in `Cfg`, so that a caller's settings reach every
branch. `source`, `push_source` and `pop_source` are not modelled, so `get_token` here has an empty
`filestack` and no `source`: those paths need file objects.
-/

namespace PyLean.TextLibs.Shlex

open PyLean

def toCps (s : String) : List Nat := s.toList.map Char.toNat

/-- The attributes `read_token` reads. -/
structure Cfg where
  posix : Bool
  commenters : List Nat
  wordchars : List Nat
  whitespace : List Nat
  whitespaceSplit : Bool
  quotes : List Nat
  escape : List Nat
  escapedquotes : List Nat
  punct : List Nat
  deriving Repr, Inhabited

/-- `self.instream`. -/
structure Src where
  data : List Nat
  failAt : Option (Nat × PyExc) := none
  deriving Repr, Inhabited

/-- `read(1)`: the character, `none` at end of file. -/
def Src.read1 (s : Src) : Py (Src × Option Nat) :=
  match s.failAt with
  | some (0, e) => .error e
  | f =>
    let f := f.map fun x => (x.1 - 1, x.2)
    match s.data with
    | [] => .ok ({ s with failAt := f }, none)
    | c :: r => .ok ({ data := r, failAt := f }, some c)

/-- `readline()`, for its effect. -/
def Src.readline (s : Src) : Py Src :=
  match s.failAt with
  | some (0, e) => .error e
  | f =>
    let f := f.map fun x => (x.1 - 1, x.2)
    let rest := s.data.dropWhile (· != 10)
    .ok { data := rest.drop 1, failAt := f }

/-- The lexer's state. `state` is `self.state`, a character or `None`. -/
structure Lx where
  src : Src
  state : Option Nat := some 32
  token : List Nat := []
  lineno : Nat := 1
  /-- `self.pushback`, left end first. -/
  pushback : List (List Nat) := []
  /-- `self._pushback_chars`, whose `pop` takes the most recent. -/
  chars : List Nat := []
  deriving Repr, Inhabited

/-- The end of the `while`, `Lib/shlex.py:283-287`. -/
def finish (c : Cfg) (l : Lx) (quoted : Bool) : Lx × Option (List Nat) :=
  let r := l.token
  ({ l with token := [] }, if c.posix && !quoted && r.isEmpty then none else some r)

mutual
  /-- `read_token`, `Lib/shlex.py:131-287`, from the top of the `while True`. -/
  def readToken (c : Cfg) : (fuel : Nat) → (quoted : Bool) → (esc : Nat) → Lx → Py (Lx × Option (List Nat))
    | 0, _, _, _ => .error .modelFuel
    | fuel + 1, quoted, esc, l =>
      if !c.punct.isEmpty && !l.chars.isEmpty then
        step c fuel quoted esc { l with chars := l.chars.dropLast } l.chars.getLast?
      else
        match l.src.read1 with
        | .error e => .error e
        | .ok (s, n) => step c fuel quoted esc { l with src := s } n

  /-- The dispatch on `self.state`, with `nextchar` read. -/
  def step (c : Cfg) : (fuel : Nat) → (quoted : Bool) → (esc : Nat) → Lx → Option Nat →
      Py (Lx × Option (List Nat))
    | fuel, quoted, esc, l0, n =>
      let l := if n == some 10 then { l0 with lineno := l0.lineno + 1 } else l0
      let emit (l : Lx) : Py (Lx × Option (List Nat)) := .ok (finish c l quoted)
      let emitOr (l : Lx) : Py (Lx × Option (List Nat)) :=
        if !l.token.isEmpty || (c.posix && quoted) then emit l
        else readToken c fuel quoted esc l
      let again (q : Bool) (e : Nat) (l : Lx) := readToken c fuel q e l
      match l.state with
      | none => emit { l with token := [] }
      | some 32 =>
        match n with
        | none => emit { l with state := none }
        | some x =>
          if c.whitespace.contains x then emitOr l
          else if c.commenters.contains x then
            match l.src.readline with
            | .error e => .error e
            | .ok s => again quoted esc { l with src := s, lineno := l.lineno + 1 }
          else if c.posix && c.escape.contains x then again quoted 97 { l with state := some x }
          else if c.wordchars.contains x then again quoted esc { l with token := [x], state := some 97 }
          else if c.punct.contains x then again quoted esc { l with token := [x], state := some 99 }
          else if c.quotes.contains x then
            again quoted esc { l with token := if c.posix then l.token else [x], state := some x }
          else if c.whitespaceSplit then again quoted esc { l with token := [x], state := some 97 }
          else emitOr { l with token := [x] }
      | some st =>
        if c.quotes.contains st then
          match n with
          | none => .error (.valueError "No closing quotation")
          | some x =>
            if x == st then
              if !c.posix then
                .ok (finish c { l with token := l.token ++ [x], state := some 32 } true)
              else again true esc { l with state := some 97 }
            else if c.posix && c.escape.contains x && c.escapedquotes.contains st then
              again true st { l with state := some x }
            else again true esc { l with token := l.token ++ [x] }
        else if c.escape.contains st then
          match n with
          | none => .error (.valueError "No escaped character")
          | some x =>
            let t := if c.quotes.contains esc && x != st && x != esc then l.token ++ [st] else l.token
            again quoted esc { l with token := t ++ [x], state := some esc }
        else if st == 97 || st == 99 then
          match n with
          | none => emit { l with state := none }
          | some x =>
            if c.whitespace.contains x then emitOr { l with state := some 32 }
            else if c.commenters.contains x then
              match l.src.readline with
              | .error e => .error e
              | .ok s =>
                let l := { l with src := s, lineno := l.lineno + 1 }
                if c.posix then emitOr { l with state := some 32 } else again quoted esc l
            else if st == 99 then
              if c.punct.contains x then again quoted esc { l with token := l.token ++ [x] }
              else
                let l := if c.whitespace.contains x then l else { l with chars := l.chars ++ [x] }
                emit { l with state := some 32 }
            else if c.posix && c.quotes.contains x then again quoted esc { l with state := some x }
            else if c.posix && c.escape.contains x then again quoted 97 { l with state := some x }
            else if c.wordchars.contains x || c.quotes.contains x ||
                (c.whitespaceSplit && !c.punct.contains x) then
              again quoted esc { l with token := l.token ++ [x] }
            else
              let l := if !c.punct.isEmpty then { l with chars := l.chars ++ [x] }
                else { l with pushback := [x] :: l.pushback }
              emitOr { l with state := some 32 }
        else again quoted esc l
end

/-- `get_token` with an empty `filestack` and no `source`, `Lib/shlex.py:99-125`. -/
def getToken (c : Cfg) (fuel : Nat) (l : Lx) : Py (Lx × Option (List Nat)) :=
  match l.pushback with
  | t :: r => .ok ({ l with pushback := r }, some t)
  | [] => readToken c fuel false 32 l

/-- `self.eof`. -/
def eofOf (c : Cfg) : Option (List Nat) := if c.posix then none else some []

/-- `list(lex)`, by `__next__`, `Lib/shlex.py:296-300`. -/
def lexAll (c : Cfg) (fuel : Nat) : (calls : Nat) → Lx → Py (List (List Nat))
  | 0, _ => .error .modelFuel
  | calls + 1, l =>
    match getToken c fuel l with
    | .error e => .error e
    | .ok (l, t) =>
      if t == eofOf c then .ok []
      else
        match lexAll c fuel calls l with
        | .error e => .error e
        | .ok r => .ok (t.getD [] :: r)

/-- `wordchars` by mode. -/
def wordcharsOf (posix : Bool) : List Nat :=
  toCps "abcdfeghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_" ++
    (if posix then toCps "ßàáâãäåæçèéêëìíîïðñòóôõöøùúûüýþÿÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÐÑÒÓÔÕÖØÙÚÛÜÝÞ" else [])

/-- What `shlex.__init__` sets, `Lib/shlex.py:23-64`, with `punctuation_chars` as a string. -/
def defaults (posix : Bool) (punct : List Nat) : Cfg :=
  let w := wordcharsOf posix
  let w := if punct.isEmpty then w else (w ++ toCps "~-./*?=").filter (!punct.contains ·)
  { posix, commenters := [35], wordchars := w, whitespace := [32, 9, 13, 10], whitespaceSplit := false,
    quotes := [39, 34], escape := [92], escapedquotes := [34], punct }

/-- The `lex` of `split`, `Lib/shlex.py:303-310`. -/
def splitCfg (comments posix : Bool) : Cfg :=
  let c := defaults posix []
  { c with whitespaceSplit := true, commenters := if comments then c.commenters else [] }

/-- `eof` starts the state as `' '`; a string becomes a `StringIO`. -/
def split (s : List Nat) (comments posix : Bool) : Py (List (List Nat)) :=
  lexAll (splitCfg comments posix) (s.length * 2 + 8) (s.length + 2) { src := { data := s } }

/-- The bytes `quote` leaves unquoted, `Lib/shlex.py:326-328`. -/
def safeChar (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 58) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) ||
    c == 37 || c == 43 || c == 44 || c == 45 || c == 46 || c == 47 || c == 61 || c == 64 || c == 95

/-- What `quote` is given. -/
inductive QArg where
  | str (s : List Nat)
  /-- Another object: its class, and what `__bool__` does. -/
  | other (cls : String) (truth : Py Bool)
  deriving Repr, Inhabited

/-- `s.replace("'", "'\"'\"'")`. -/
def quoteBody (s : List Nat) : List Nat :=
  s.flatMap fun c => if c == 39 then [39, 34, 39, 34, 39] else [c]

/-- `quote`, `Lib/shlex.py:321-338`, on a `str`. -/
def quoteS (s : List Nat) : List Nat :=
  if s.isEmpty then [39, 39]
  else if s.all safeChar then s
  else 39 :: quoteBody s ++ [39]

/-- `quote`: `if not s` comes before the type check, so any false object is `''`. -/
def quote : QArg → Py (List Nat)
  | .str s => .ok (quoteS s)
  | .other cls t =>
    match t with
    | .error e => .error e
    | .ok false => .ok [39, 39]
    | .ok true => .error (.typeError s!"expected string object, got '{cls}'")

/-- `join`, `Lib/shlex.py:316-318`. -/
def joinS (args : List (List Nat)) : List Nat := List.intercalate [32] (args.map quoteS)

end PyLean.TextLibs.Shlex
