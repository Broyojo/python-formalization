import PyLean.Core
import PyLean.UnicodeObj.TextCase

/-!
Model of the pure part of `Lib/posixpath.py`, `Lib/ntpath.py` and `Lib/genericpath.py`, CPython 3.14.7,
with `_Py_normpath_and_size`, `Python/fileutils.c:2520-2632`, as the `posix` build runs it.

Values keep their kind, because `str` and `bytes` do not mix: `ntpath.join` can raise or succeed on a
mix, depending on which operation meets it. `__fspath__` is a callback, so it can raise or return
anything. Only `Lib/ntpath.py`'s pure-Python functions run here: the `nt` module's C versions exist
on Windows only, and are cited where they differ.
-/

namespace PyLean.TextLibs.Path

open PyLean

/-- A `str` or a `bytes`. -/
structure PV where
  isb : Bool
  s : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- What a path argument is. `fsp` is an object with `__fspath__`, and `other` one without. -/
inductive PathArg where
  | val (v : PV)
  | fsp (cls : String) (r : Py (Option PV)) (bad : String)
  | other (cls : String)
  deriving Repr, Inhabited

/-- `PyOS_FSPath`, `Modules/posixmodule.c`. `r` is `none` when `__fspath__` returned an object of type
`bad`. -/
def fspath : PathArg → Py PV
  | .val v => .ok v
  | .other c => .error (.typeError s!"expected str, bytes or os.PathLike object, not {c}")
  | .fsp c r bad =>
    match r with
    | .error e => .error e
    | .ok (some v) => .ok v
    | .ok none => .error (.typeError s!"expected {c}.__fspath__() to return str or bytes, not {bad}")

def mixErr : PyExc := .typeError "Can't mix strings and bytes in path components"

/-- The class name of what `_check_arg_types` sees. -/
def argCheck (fn : String) (args : List PathArg) : Py Unit :=
  let rec go : List PathArg → Bool → Bool → Py Unit
    | [], hs, hb => if hs && hb then .error mixErr else .ok ()
    | .val v :: r, hs, hb => if v.isb then go r hs true else go r true hb
    | .fsp c _ _ :: r, _, _ => .error (.typeError s!"{fn}() argument must be str, bytes, or os.PathLike object, not '{c}'")
    | .other c :: r, _, _ => .error (.typeError s!"{fn}() argument must be str, bytes, or os.PathLike object, not '{c}'")
  go args false false

/-- `s.rfind(c)`, or `-1`. -/
def rfind (c : Nat) (s : List Nat) : Int :=
  match s.reverse.findIdx? (· == c) with
  | some i => (s.length : Int) - 1 - i
  | none => -1

/-- `s.rstrip(cs)`. -/
def rstrip (p : Nat → Bool) (s : List Nat) : List Nat := (s.reverse.dropWhile p).reverse

/-! ### `genericpath` -/

/-- The last separator of `_splitext`, `Lib/genericpath.py:174-177`. -/
def sepIdx (p : List Nat) (sep : Nat) (altsep : Option Nat) : Int :=
  match altsep with
  | some a => max (rfind sep p) (rfind a p)
  | none => rfind sep p

/-- `_splitext`, `Lib/genericpath.py:167-188`. -/
def splitextL (p : List Nat) (sep : Nat) (altsep : Option Nat) : List Nat × List Nat :=
  let sepIndex := sepIdx p sep altsep
  let dotIndex := rfind 46 p
  if dotIndex > sepIndex then
    let start := (sepIndex + 1).toNat
    let rec go : (fuel i : Nat) → Bool
      | 0, _ => false
      | fuel + 1, i =>
        if (i : Int) < dotIndex then
          if p.getD i 0 != 46 then true else go fuel (i + 1)
        else false
    if go p.length start then (p.take dotIndex.toNat, p.drop dotIndex.toNat) else (p, [])
  else (p, [])

/-! ### `posixpath` -/

def isSepP (c : Nat) : Bool := c == 47

/-- `_path_splitroot_ex` on POSIX, `Python/fileutils.c`, and the fallback at `Lib/posixpath.py:146-162`. -/
def splitrootP (p : List Nat) : List Nat × List Nat × List Nat :=
  match p with
  | 47 :: 47 :: 47 :: _ => ([], [47], p.drop 1)
  | 47 :: 47 :: _ => ([], [47, 47], p.drop 2)
  | 47 :: _ => ([], [47], p.drop 1)
  | _ => ([], [], p)

/-- `posixpath.isabs`, `Lib/posixpath.py:59-63`. -/
def isabsP (a : PathArg) : Py Bool := do
  let v ← fspath a
  return v.s.head? == some 47

/-- `posixpath.split`, `Lib/posixpath.py:97-106`. -/
def splitP (a : PathArg) : Py (PV × PV) := do
  let v ← fspath a
  let i := (rfind 47 v.s + 1).toNat
  let head := v.s.take i
  let tail := v.s.drop i
  let head := if !head.isEmpty && head != List.replicate head.length 47 then rstrip isSepP head else head
  return (⟨v.isb, head⟩, ⟨v.isb, tail⟩)

/-- `posixpath.splitext`, `Lib/posixpath.py:113-121`. -/
def splitextP (a : PathArg) : Py (PV × PV) := do
  let v ← fspath a
  let (r, e) := splitextL v.s 47 none
  return (⟨v.isb, r⟩, ⟨v.isb, e⟩)

/-- `posixpath.basename`, `Lib/posixpath.py@3.14.7:166-171`. -/
def basenameP (a : PathArg) : Py PV := do
  let v ← fspath a
  return ⟨v.isb, v.s.drop (rfind 47 v.s + 1).toNat⟩

/-- `posixpath.dirname`, `Lib/posixpath.py@3.14.7:176-184`. -/
def dirnameP (a : PathArg) : Py PV := do
  let v ← fspath a
  let i := (rfind 47 v.s + 1).toNat
  let head := v.s.take i
  return ⟨v.isb, if !head.isEmpty && head != List.replicate head.length 47 then rstrip isSepP head else head⟩

/-- The body of the `for b in p` of `posixpath.join`, `Lib/posixpath.py:75-85`. `none` is a `TypeError`
in the `try`, from mixing kinds or from `os.fspath`; `some (.error e)` is any other exception. -/
def joinStep (sep : PV) (path : PV) (b : PathArg) : Option (Py PV) :=
  match fspath b with
  | .error (.typeError _) => none
  | .error (.named "AttributeError" _) => none
  | .error e => some (.error e)
  | .ok b =>
    if b.isb != sep.isb then none
    else if b.s.head? == some 47 ∨ path.s.isEmpty then
      some (.ok b)
    else if path.isb != sep.isb then none
    else if path.s.getLast? == some 47 then some (.ok ⟨sep.isb, path.s ++ b.s⟩)
    else some (.ok ⟨sep.isb, path.s ++ [47] ++ b.s⟩)

/-- `posixpath.join`, `Lib/posixpath.py:67-89`. -/
def joinP (a : PathArg) (ps : List PathArg) : Py PV := do
  let a0 ← fspath a
  let sep : PV := ⟨a0.isb, [47]⟩
  let rec go : List PathArg → PV → Option (Py PV)
    | [], path => some (.ok path)
    | b :: r, path =>
      match joinStep sep path b with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok path) => go r path
  match go ps a0 with
  | some x => x
  | none =>
    argCheck "join" (.val a0 :: ps)
    -- `raise`: the exception caught, when the check finds nothing wrong.
    .error (.typeError "~path join")

/-- The fallback `normpath`, `Lib/posixpath.py:345-371`. -/
def normpathPy (p : List Nat) : List Nat :=
  if p.isEmpty then [46]
  else
    let (_, root, rest) := splitrootP p
    let comps := rest.splitOn 47
    let step (acc : List (List Nat)) (c : List Nat) : List (List Nat) :=
      if c.isEmpty || c == [46] then acc
      else if c != [46, 46] || (root.isEmpty && acc.isEmpty) ||
          (!acc.isEmpty && acc.getLast? == some [46, 46]) then acc ++ [c]
      else if !acc.isEmpty then acc.dropLast
      else acc
    let out := root ++ List.intercalate [47] (comps.foldl step [])
    if out.isEmpty then [46] else out

/-- `SEP_OR_END`. -/
def sepOrEnd (l : List Nat) : Bool :=
  match l with
  | [] => true
  | c :: _ => c == 47

/-- The back scan of `..`, `Python/fileutils.c:2591-2592`: `p3`, an index in `out`. -/
def backScan (out : List Nat) (m : Nat) : Nat :=
  let rec first : (fuel i : Nat) → Nat
    | 0, i => i
    | fuel + 1, i =>
      if i == m then i
      else if out.getD (i - 1) 0 == 47 then first fuel (i - 1)
      else i - 1
  let rec second : (fuel i : Nat) → Nat
    | 0, i => i
    | fuel + 1, i =>
      if i != m && out.getD (i - 1) 0 != 47 then second fuel (i - 1) else i
  second out.length (first out.length out.length)

/-- The `for` of `_Py_normpath_and_size`, `Python/fileutils.c:2578-2619`. `out` is `path[:p2]`, `m` is
`minP2`, and `lastC` the last character seen. -/
def cLoop (m : Nat) : (fuel : Nat) → List Nat → List Nat → Nat → List Nat
  | 0, _, out, _ => out
  | _ + 1, [], out, _ => out
  | fuel + 1, c :: r, out, lastC =>
    if lastC == 47 then
      if c == 46 then
        let sep1 := sepOrEnd r
        let sep2 := !sep1 && sepOrEnd (r.drop 1)
        if sep2 && r.head? == some 46 then
          let p3 := backScan out m
          let prevUp := out.getD p3 0 == 46 && out.getD (p3 + 1) 0 == 46 && out.getD (p3 + 2) 0 == 47
          if out.length == m || prevUp then cLoop m fuel (r.drop 1) (out ++ [46, 46]) 46
          else if out.getD p3 0 == 47 then cLoop m fuel (r.drop 1) (out.take (p3 + 1)) lastC
          else cLoop m fuel (r.drop 1) (out.take p3) lastC
        else if sep1 then cLoop m fuel r out lastC
        else cLoop m fuel r (out ++ [c]) c
      else if c == 47 then cLoop m fuel r out lastC
      else cLoop m fuel r (out ++ [c]) c
    else cLoop m fuel r (out ++ [c]) c

/-- The strip at the end, `Python/fileutils.c:2620-2627`: how much of `out` stays. -/
def cTrim (out : List Nat) (m : Nat) : List Nat :=
  if out.length != m then
    let rec go : (fuel i : Nat) → Nat
      | 0, i => i
      | fuel + 1, i =>
        if i - 1 != m && out.getD (i - 1) 0 == 47 then go fuel (i - 1) else i
    out.take (go out.length out.length)
  else out.take m

/-- `_Py_normpath_and_size`, with the `'.'` of `os__path_normpath_impl` for an empty result. -/
def normpathC (p : List Nat) : List Nat :=
  if p.isEmpty then [46]
  else
    let (_, root, rest) := splitrootP p
    let m := if root.isEmpty then 0 else root.length - 1
    let lastC0 := if root.isEmpty then 0 else 47
    let (rest, lastC) :=
      match rest with
      | 46 :: r =>
        if sepOrEnd r then
          (r.dropWhile (· == 47), r.headD 0)
        else (rest, lastC0)
      | _ => (rest, lastC0)
    let out := cTrim (cLoop m (rest.length + 1) rest root lastC) m
    if out.isEmpty then [46] else out

/-! ### `ntpath` -/

def isSepN (c : Nat) : Bool := c == 92 || c == 47

def toBack (s : List Nat) : List Nat := s.map fun c => if c == 47 then 92 else c

def upperA (s : List Nat) : List Nat := s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `s.find(sep, start)`, as an index. -/
def findFrom (c : Nat) (s : List Nat) (start : Nat) : Option Nat :=
  ((s.drop start).findIdx? (· == c)).map (· + start)

/-- The fallback `splitroot`, `Lib/ntpath.py:176-213`. -/
def splitrootN (p : List Nat) : List Nat × List Nat × List Nat :=
  let n := toBack p
  if n.head? == some 92 then
    if n.getD 1 0 == 92 ∧ n.length > 1 then
      let start := if upperA (n.take 8) == [92, 92, 63, 92, 85, 78, 67, 92] then 8 else 2
      match findFrom 92 n start with
      | none => (p, [], [])
      | some i =>
        match findFrom 92 n (i + 1) with
        | none => (p, [], [])
        | some j => (p.take j, (p.drop j).take 1, p.drop (j + 1))
    else ([], p.take 1, p.drop 1)
  else if n.length > 1 ∧ n.getD 1 0 == 58 then
    if n.length > 2 ∧ n.getD 2 0 == 92 then (p.take 2, (p.drop 2).take 1, p.drop 3)
    else (p.take 2, [], p.drop 2)
  else ([], [], p)

/-- `ntpath.isabs`, `Lib/ntpath.py@3.14.7:80-94`. -/
def isabsN (a : PathArg) : Py Bool := do
  let v ← fspath a
  let s := toBack (v.s.take 3)
  return (s.drop 1).take 2 == [58, 92] || s.take 2 == [92, 92]

/-- `ntpath.split`, `Lib/ntpath.py:222-235`. -/
def splitN (a : PathArg) : Py (PV × PV) := do
  let v ← fspath a
  let (d, r, p) := splitrootN v.s
  let tailLen := (p.reverse.takeWhile (fun c => !isSepN c)).length
  let i := p.length - tailLen
  return (⟨v.isb, d ++ r ++ rstrip isSepN (p.take i)⟩, ⟨v.isb, p.drop i⟩)

/-- `ntpath.splitext`, `Lib/ntpath.py:243-247`. -/
def splitextN (a : PathArg) : Py (PV × PV) := do
  let v ← fspath a
  let (r, e) := splitextL v.s 92 (some 47)
  return (⟨v.isb, r⟩, ⟨v.isb, e⟩)

/-- The fallback `normpath`, `Lib/ntpath.py:477-511`. -/
def normpathN (p : List Nat) : List Nat :=
  let (d, root, rest) := splitrootN (toBack p)
  let pre := d ++ root
  let comps := rest.splitOn 92
  let rec go : (fuel : Nat) → List (List Nat) → List (List Nat) → List (List Nat)
    | 0, acc, _ => acc
    | _ + 1, acc, [] => acc
    | fuel + 1, acc, c :: r =>
      if c.isEmpty || c == [46] then go fuel acc r
      else if c == [46, 46] then
        if !acc.isEmpty && acc.getLast? != some [46, 46] then go fuel acc.dropLast r
        else if acc.isEmpty && !root.isEmpty then go fuel acc r
        else go fuel (acc ++ [c]) r
      else go fuel (acc ++ [c]) r
  let out := go comps.length [] comps
  let out := if pre.isEmpty && out.isEmpty then [[46]] else out
  pre ++ List.intercalate [92] out

/-- `.lower()` of a drive, for its kind: `bytes` is ASCII, and `str` is the Unicode mapping. -/
def lowerD (v : PV) : List Nat :=
  if v.isb then v.s.map fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
  else match PyLean.UnicodeObj.unicodeLower v.s with
    | .ok t => t
    | .error _ => v.s

/-- `a + b`: `none` for the `TypeError` of a mix. -/
def cat (a b : PV) : Option PV := if a.isb == b.isb then some ⟨a.isb, a.s ++ b.s⟩ else none

/-- The state of `ntpath.join`: drive, root and path, each of whatever kind it came from. -/
structure JSt where
  d : PV
  r : PV
  p : PV
  deriving Repr, Inhabited

/-- One `p` of the `for`, `Lib/ntpath.py:113-132`. `none` is a `TypeError` in the `try`. `isb` is the
kind of `seps`. -/
def joinStepN (isb : Bool) (st : JSt) (q : PV) : Option JSt :=
  let (d, r, t) := splitrootN q.s
  let pd : PV := ⟨q.isb, d⟩
  let pr : PV := ⟨q.isb, r⟩
  let pp : PV := ⟨q.isb, t⟩
  if !pr.s.isEmpty then
    some { d := if !pd.s.isEmpty || st.d.s.isEmpty then pd else st.d, r := pr, p := pp }
  else
    let relative (d : PV) : Option JSt := do
      let rp ←
        if !st.p.s.isEmpty then
          if st.p.isb != isb then none
          else if (st.p.s.getLast?.map isSepN) == some true then some st.p
          else cat st.p ⟨isb, [92]⟩
        else some st.p
      let np ← cat rp pp
      return { st with d, p := np }
    if !pd.s.isEmpty && pd != st.d then
      if lowerD pd != lowerD st.d || pd.isb != st.d.isb then some { d := pd, r := pr, p := pp }
      else relative pd
    else relative st.d

/-- `ntpath.join`, `Lib/ntpath.py:98-145`. -/
def joinN (a : PathArg) (ps : List PathArg) : Py PV := do
  let a0 ← fspath a
  let e0 : PV := ⟨a0.isb, []⟩
  let (d, r, t) := splitrootN a0.s
  let rec go : List PathArg → JSt → Option (Py JSt)
    | [], st => some (.ok st)
    | b :: rest, st =>
      match fspath b with
      | .error (.typeError _) => none
      | .error (.named "AttributeError" _) => none
      | .error e => some (.error e)
      | .ok q =>
        match joinStepN a0.isb st q with
        | none => none
        | some st => go rest st
  let finish (st : JSt) : Option PV :=
    if !st.p.s.isEmpty && st.r.s.isEmpty && !st.d.s.isEmpty then
      if st.d.isb != a0.isb then none
      else if (st.d.s.getLast?.map fun c => c == 58 || isSepN c) == some true then
        (cat st.d st.r).bind (cat · st.p)
      else (cat st.d ⟨a0.isb, [92]⟩).bind (cat · st.p)
    else (cat st.d st.r).bind (cat · st.p)
  let failed : Py PV := do
    argCheck "join" (.val a0 :: ps)
    .error (.typeError "~path join")
  match go ps ⟨⟨a0.isb, d⟩, ⟨a0.isb, r⟩, ⟨a0.isb, t⟩⟩ with
  | none => failed
  | some (.error e) => .error e
  | some (.ok st) =>
    match finish st with
    | some v => .ok v
    | none => failed

end PyLean.TextLibs.Path
