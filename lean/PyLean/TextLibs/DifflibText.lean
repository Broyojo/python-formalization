import PyLean.TextLibs.DifflibObj
import PyLean.Binary64.Model
import PyLean.UnicodeObj.Ctype

/-!
The text functions of `Lib/difflib.py`, on the matcher over objects: `unified_diff`, `context_diff`,
`Differ`, `ndiff`, `restore`, `IS_LINE_JUNK`, `IS_CHARACTER_JUNK` and `get_close_matches`.

A `str` is its code points. The matcher runs over lines, and in `Differ` over characters, as objects
whose `__hash__` and `__eq__` never raise. `hash` of a `str` is not modelled: the result of the matcher
does not depend on it, which `DifflibObjSim.lean` proves, so `strOps` hashes everything to 0 and every
key is compared. Scope limits: `color=True` of `unified_diff`, whose output depends on the environment;
a negative `n`; `Differ` on anything but lists of `str`; and identical line objects, which only spare
`set_seq1` and `set_seq2` some work, as the callbacks are functions of the character.
-/

namespace PyLean.TextLibs.Difflib

open PyLean PyLean.Binary64

abbrev Str := List Nat

/-- A line of `unified_diff` and `context_diff`. `_check_types` looks at the first line only, so others can
be anything: `other` has the type name, `format()` of the object, and whether it is hashable. -/
inductive LineO where
  | str (s : Str)
  | other (ty : String) (text : Str) (hashable : Bool)
  deriving DecidableEq, Repr, Inhabited

def LineO.text : LineO → Str
  | .str s => s
  | .other _ t _ => t

/-- Lines as objects. -/
def lineOps : Ops LineO where
  hash
    | .other ty _ false => .error (.typeError s!"cannot use '{ty}' as a dict key (unhashable type: '{ty}')")
    | _ => .ok 0
  eq x y := .ok (decide (x = y))
  same x y := decide (x = y)

/-- A line of `Differ`. -/
def strOps : Ops Str where
  hash _ := .ok 0
  eq x y := .ok (decide (x = y))
  same x y := decide (x = y)

/-- One character of a line. -/
def charOps : Ops Nat where
  hash c := .ok c
  eq x y := .ok (x == y)
  same x y := x == y

/-- `str(n)`. -/
def num (n : Nat) : Str := (toString n).toList.map Char.toNat

def sliceL {β : Type} (l : List β) (i j : Nat) : List β := (l.drop i).take (j - i)

/-- `_format_range_unified`, `Lib/difflib.py:1090-1098`. -/
def fmtRangeU (start stop : Nat) : Str :=
  let beginning := start + 1
  let length := stop - start
  if length = 1 then num beginning
  else
    let beginning := if length = 0 then beginning - 1 else beginning
    num beginning ++ [44] ++ num length

/-- `_format_range_context`, `Lib/difflib.py:1183-1191`. -/
def fmtRangeC (start stop : Nat) : Str :=
  let beginning := start + 1
  let length := stop - start
  let beginning := if length = 0 then beginning - 1 else beginning
  if length ≤ 1 then num beginning
  else num beginning ++ [44] ++ num (beginning + length - 1)

/-- A sequence argument of `unified_diff`. -/
inductive SeqArg where
  | lines (l : List LineO)
  | str (s : Str)
  deriving DecidableEq, Repr

/-- A file name or date, or `lineterm`. -/
inductive TextArg where
  | str (s : Str)
  | other (repr : String)
  deriving DecidableEq, Repr

/-- `a and not isinstance(a[0], str)`, then `isinstance(a, str)`, `Lib/difflib.py:1278-1287`. `a` being a
`str`, its first item is one. -/
def checkFirst : SeqArg → Py Unit
  | .lines (.other ty t _ :: _) =>
    .error (.typeError s!"lines to compare must be str, not {ty} ({String.ofList (t.map Char.ofNat)})")
  | _ => .ok ()

def checkSeq : SeqArg → Py Unit
  | .str _ => .error (.typeError "input must be a sequence of strings, not str")
  | _ => .ok ()

/-- `for arg in args`, `Lib/difflib.py:1290-1292`. -/
def checkArgs : List TextArg → Py Unit
  | [] => .ok ()
  | .str _ :: r => checkArgs r
  | .other x :: _ => .error (.typeError s!"all arguments must be str, not: {x}")

/-- `_check_types`, `Lib/difflib.py:1271-1292`. -/
def checkTypes (a b : SeqArg) (args : List TextArg) : Py Unit := do
  checkFirst a
  checkFirst b
  checkSeq a
  checkSeq b
  checkArgs args

def seqLines : SeqArg → List LineO
  | .lines l => l
  | .str _ => []

def textOf : TextArg → Str
  | .str s => s
  | .other _ => []

/-- `'\t{}'.format(date) if date else ''`. -/
def dateOf (d : Str) : Str := if d.isEmpty then [] else 9 :: d

/-- The lines of a hunk of `unified_diff`, `Lib/difflib.py:1169-1179`. The f-strings format a line that
is not a `str`, where `'-' + line` used to raise. -/
def bodyU (a b : List LineO) : List Op → List Str
  | [] => []
  | (t, i1, i2, j1, j2) :: r =>
    let minus := (sliceL a i1 i2).map fun l => 45 :: l.text
    let plus := (sliceL b j1 j2).map fun l => 43 :: l.text
    let x : List Str :=
      match t with
      | .equal => (sliceL a i1 i2).map fun l => 32 :: l.text
      | .replace => minus ++ plus
      | .delete => minus
      | .insert => plus
    x ++ bodyU a b r

/-- A hunk of `unified_diff`, `Lib/difflib.py:1164-1179`. -/
def hunkU (a b : List LineO) (lt : Str) (g : List Op) : List Str :=
  let f := g.headD (.equal, 0, 0, 0, 0)
  let l := g.getLastD (.equal, 0, 0, 0, 0)
  (toS "@@ -" ++ fmtRangeU f.2.1 l.2.2.1 ++ toS " +" ++ fmtRangeU f.2.2.2.1 l.2.2.2.2 ++ toS " @@" ++ lt) :: bodyU a b g
where
  toS (s : String) : Str := s.toList.map Char.toNat

def toStr (s : String) : Str := s.toList.map Char.toNat

/-- `unified_diff`, `Lib/difflib.py:1101-1179`, with `color=False`. Everything that can fail happens
before the first line is yielded. -/
def unifiedDiff (a b : SeqArg) (fromfile tofile fromdate todate : TextArg) (n : Nat) (lineterm : TextArg) :
    Py (List Str) := do
  checkTypes a b [fromfile, tofile, fromdate, todate, lineterm]
  let la := seqLines a
  let lb := seqLines b
  let s ← makeO lineOps none la lb true
  let gs ← (getGroupedO lineOps s n).2
  let lt := textOf lineterm
  if gs.isEmpty then return []
  let head : List Str :=
    [toStr "--- " ++ textOf fromfile ++ dateOf (textOf fromdate) ++ lt,
     toStr "+++ " ++ textOf tofile ++ dateOf (textOf todate) ++ lt]
  return head ++ gs.flatMap (hunkU la lb lt)

/-- What a generator has yielded, and how it ended. -/
abbrev Emit := List Str × Py Unit

def Emit.and (x : Emit) (y : Emit) : Emit :=
  match x.2 with
  | .error e => x
  | .ok () => (x.1 ++ y.1, y.2)

/-- The lines of one side of `context_diff`: `prefix[tag] + line`, which raises on anything but a `str`. -/
def plusLines (p : Str) : List LineO → Emit
  | [] => ([], .ok ())
  | .str s :: r => Emit.and ([p ++ s], .ok ()) (plusLines p r)
  | .other ty _ _ :: _ => ([], .error (.typeError s!"can only concatenate str (not \"{ty}\") to str"))

def prefixC : Tag → Str
  | .insert => toStr "+ "
  | .delete => toStr "- "
  | .replace => toStr "! "
  | .equal => toStr "  "

def sideA (a : List LineO) : List Op → Emit
  | [] => ([], .ok ())
  | (t, i1, i2, _, _) :: r =>
    if t != .insert then Emit.and (plusLines (prefixC t) (sliceL a i1 i2)) (sideA a r)
    else sideA a r

def sideB (b : List LineO) : List Op → Emit
  | [] => ([], .ok ())
  | (t, _, _, j1, j2) :: r =>
    if t != .delete then Emit.and (plusLines (prefixC t) (sliceL b j1 j2)) (sideB b r)
    else sideB b r

/-- A hunk of `context_diff`, `Lib/difflib.py:1254-1269`. -/
def hunkC (a b : List LineO) (lt : Str) (g : List Op) : Emit :=
  let f := g.headD (.equal, 0, 0, 0, 0)
  let l := g.getLastD (.equal, 0, 0, 0, 0)
  let h1 : List Str := [toStr "***************" ++ lt, toStr "*** " ++ fmtRangeC f.2.1 l.2.2.1 ++ toStr " ****" ++ lt]
  let x : Emit := if g.any (fun o => o.1 == .replace || o.1 == .delete) then sideA a g else ([], .ok ())
  let h2 : List Str := [toStr "--- " ++ fmtRangeC f.2.2.2.1 l.2.2.2.2 ++ toStr " ----" ++ lt]
  let y : Emit := if g.any (fun o => o.1 == .replace || o.1 == .insert) then sideB b g else ([], .ok ())
  Emit.and (h1, .ok ()) (Emit.and x (Emit.and (h2, .ok ()) y))

def hunksC (a b : List LineO) (lt : Str) : List (List Op) → Emit
  | [] => ([], .ok ())
  | g :: r => Emit.and (hunkC a b lt g) (hunksC a b lt r)

/-- `context_diff`, `Lib/difflib.py:1195-1269`. -/
def contextDiff (a b : SeqArg) (fromfile tofile fromdate todate : TextArg) (n : Nat) (lineterm : TextArg) : Emit :=
  match checkTypes a b [fromfile, tofile, fromdate, todate, lineterm] with
  | .error e => ([], .error e)
  | .ok () =>
    let la := seqLines a
    let lb := seqLines b
    match makeO lineOps none la lb true with
    | .error e => ([], .error e)
    | .ok s =>
      match (getGroupedO lineOps s n).2 with
      | .error e => ([], .error e)
      | .ok gs =>
        let lt := textOf lineterm
        if gs.isEmpty then ([], .ok ())
        else
          Emit.and ([toStr "*** " ++ textOf fromfile ++ dateOf (textOf fromdate) ++ lt,
                     toStr "--- " ++ textOf tofile ++ dateOf (textOf todate) ++ lt], .ok ()) (hunksC la lb lt gs)

/-! ### `Differ` -/

def two : F64 := F64.ofBits 0x4000000000000000

/-- `cutoff = 0.74999`, `Lib/difflib.py:921`. -/
def fancyCutoff : F64 := F64.ofBits 0x3fe7ffeb074a771d

/-- `_calculate_ratio`, `Lib/difflib.py:40-43`. -/
def calcRatio (m length : Nat) : F64 :=
  if length = 0 then F64.one else F64.div (F64.mul two (F64.ofInt m)) (F64.ofInt length)

/-- `_dump`, `Lib/difflib.py:877-880`, with the tag as a code point. -/
def dump (tag : Nat) (x : List Str) (lo hi : Nat) : List Str :=
  (sliceL x lo hi).map fun l => tag :: 32 :: l

/-- `_plain_replace`, `Lib/difflib.py:882-894`. -/
def plainReplace (a : List Str) (alo ahi : Nat) (b : List Str) (blo bhi : Nat) : List Str :=
  if bhi - blo < ahi - alo then dump 43 b blo bhi ++ dump 45 a alo ahi
  else dump 45 a alo ahi ++ dump 43 b blo bhi

/-- `_fancy_helper`, `Lib/difflib.py:990-1000`. -/
def fancyHelper (a : List Str) (alo ahi : Nat) (b : List Str) (blo bhi : Nat) : List Str :=
  if alo < ahi then
    if blo < bhi then plainReplace a alo ahi b blo bhi else dump 45 a alo ahi
  else if blo < bhi then dump 43 b blo bhi
  else []

/-- `_keep_original_ws`, `Lib/difflib.py:718-723`. -/
def keepWs (s tags : Str) : Str :=
  (s.zip tags).map fun p => if p.2 == 32 && PyLean.UnicodeObj.isSpace p.1 then p.1 else p.2

/-- `s.rstrip()`. -/
def rstripS (s : Str) : Str := (s.reverse.dropWhile PyLean.UnicodeObj.isSpace).reverse

/-- `s.strip()`. -/
def stripS (s : Str) : Str := rstripS (s.dropWhile PyLean.UnicodeObj.isSpace)

/-- `_qformat`, `Lib/difflib.py:1002-1027`. -/
def qformat (aline bline atags btags : Str) : List Str :=
  let at' := rstripS (keepWs aline atags)
  let bt := rstripS (keepWs bline btags)
  [45 :: 32 :: aline] ++ (if at'.isEmpty then [] else [63 :: 32 :: (at' ++ [10])]) ++
    [43 :: 32 :: bline] ++ (if bt.isEmpty then [] else [63 :: 32 :: (bt ++ [10])])

/-- The tag strings of `_fancy_replace`, `Lib/difflib.py:965-977`. -/
def tagsOf : List Op → Str × Str
  | [] => ([], [])
  | (t, i1, i2, j1, j2) :: r =>
    let la := i2 - i1
    let lb := j2 - j1
    let x := tagsOf r
    match t with
    | .replace => (List.replicate la 94 ++ x.1, List.replicate lb 94 ++ x.2)
    | .delete => (List.replicate la 45 ++ x.1, x.2)
    | .insert => (x.1, List.replicate lb 43 ++ x.2)
    | .equal => (List.replicate la 32 ++ x.1, List.replicate lb 32 ++ x.2)

/-- `for i in arange`, `Lib/difflib.py:940-949`: the best `i`, and the best ratio, which starts at the cutoff. -/
def innerBest (a : List Str) (s : SMO Nat) : List Nat → Option Nat → F64 → Py (SMO Nat × Option Nat × F64)
  | [], bi, br => .ok (s, bi, br)
  | i :: r, bi, br =>
    let s := setSeq1O s (a.getD i []) false
    let la := s.a.length
    let lb := s.b.length
    if F64.le (calcRatio (min la lb) (la + lb)) br then innerBest a s r bi br
    else
      match quickPairO charOps s with
      | (_, .error e) => .error e
      | (s, .ok (m, l)) =>
        if F64.le (calcRatio m l) br then innerBest a s r bi br
        else
          match ratioPairO charOps s with
          | .error e => .error e
          | .ok (s, m, l) =>
            let ratio := calcRatio m l
            if F64.gt ratio br then innerBest a s r (some i) ratio
            else innerBest a s r bi br

/-- The `for j in range(blo, bhi)` of `_fancy_replace`, `Lib/difflib.py:929-985`: what it yields, and
`dump_i`, `dump_j` at the end. `fuel` is what is left of the range. -/
def fancyLoop (a b : List Str) (alo ahi blo : Nat) : (fuel : Nat) → (j : Nat) → SMO Nat → Nat → Nat →
    List Str × Py (Nat × Nat)
  | 0, _, _, di, dj => ([], .ok (di, dj))
  | fuel + 1, j, s, di, dj =>
    match setSeq2O charOps s (b.getD j []) false with
    | (_, .error e) => ([], .error e)
    | (s, .ok ()) =>
      let aequiv := alo + (j - blo)
      let lo := max (aequiv - 10) di
      let hi := min (aequiv + 11) ahi
      if hi ≤ lo then ([], .ok (di, dj))
      else
        match innerBest a s (List.range' lo (hi - lo)) none fancyCutoff with
        | .error e => ([], .error e)
        | .ok (s, none, _) => fancyLoop a b alo ahi blo fuel (j + 1) s di dj
        | .ok (s, some bi, _) =>
          let help := fancyHelper a di bi b dj j
          let aelt := a.getD bi []
          let belt := b.getD j []
          if aelt != belt then
            match setSeqsO charOps s aelt belt false false with
            | (_, .error e) => (help, .error e)
            | (s, .ok ()) =>
              match getOpcodesO charOps s with
              | (_, .error e) => (help, .error e)
              | (s, .ok ops) =>
                let t := tagsOf ops
                let x := fancyLoop a b alo ahi blo fuel (j + 1) s (bi + 1) (j + 1)
                (help ++ qformat aelt belt t.1 t.2 ++ x.1, x.2)
          else
            let x := fancyLoop a b alo ahi blo fuel (j + 1) s (bi + 1) (j + 1)
            (help ++ [32 :: 32 :: aelt] ++ x.1, x.2)

/-- `_fancy_replace`, `Lib/difflib.py:896-988`. -/
def fancyReplace (charjunk : Option (Nat → Py Bool)) (a : List Str) (alo ahi : Nat) (b : List Str) (blo bhi : Nat) : Emit :=
  match makeO charOps charjunk [] [] true with
  | .error e => ([], .error e)
  | .ok s =>
    let x := fancyLoop a b alo ahi blo (bhi - blo) blo s alo blo
    match x.2 with
    | .error e => (x.1, .error e)
    | .ok (di, dj) => (x.1 ++ fancyHelper a di ahi b dj bhi, .ok ())

/-- The `for` of `Differ.compare`, `Lib/difflib.py:862-875`. -/
def compareOps (charjunk : Option (Nat → Py Bool)) (a b : List Str) : List Op → Emit
  | [] => ([], .ok ())
  | (t, alo, ahi, blo, bhi) :: r =>
    let g : Emit :=
      match t with
      | .replace => fancyReplace charjunk a alo ahi b blo bhi
      | .delete => (dump 45 a alo ahi, .ok ())
      | .insert => (dump 43 b blo bhi, .ok ())
      | .equal => (dump 32 a alo ahi, .ok ())
    Emit.and g (compareOps charjunk a b r)

/-- `Differ.compare`, `Lib/difflib.py:836-875`, and so `ndiff`, `Lib/difflib.py:1324-1359`. -/
def compareO (linejunk : Option (Str → Py Bool)) (charjunk : Option (Nat → Py Bool)) (a b : List Str) : Emit :=
  match makeO strOps linejunk a b true with
  | .error e => ([], .error e)
  | .ok s =>
    match getOpcodesO strOps s with
    | (_, .error e) => ([], .error e)
    | (_, .ok ops) => compareOps charjunk a b ops

/-- The `for` of `restore`, `Lib/difflib.py:2103-2105`. -/
def restoreL (tag : Str) (ds : List Str) : List Str :=
  ds.filterMap fun line =>
    if line.take 2 == [32, 32] || line.take 2 == tag then some (line.drop 2) else none

/-- `restore`, `Lib/difflib.py:2075-2105`. -/
def restoreO (delta : List Str) (which : Int) : Py (List Str) :=
  if which = 1 then .ok (restoreL [45, 32] delta)
  else if which = 2 then .ok (restoreL [43, 32] delta)
  else .error (.valueError "~unknown delta choice (must be 1 or 2)")

/-- `IS_LINE_JUNK`, `Lib/difflib.py:1046-1065`, with no `pat`: `line.strip() in '#'`. -/
def isLineJunk (line : Str) : Bool :=
  let s := stripS line
  s.isEmpty || s == [35]

/-- `IS_CHARACTER_JUNK`, `Lib/difflib.py:1067-1081`, on a character. -/
def isCharJunk (c : Nat) : Bool := c == 32 || c == 9

/-! ### `get_close_matches` -/

/-- `_nlargest` on `(ratio, x)`: largest first. Ties on the ratio go by `x`, and equal pairs are the same. -/
def insertBest (x : F64 × Str) : List (F64 × Str) → List (F64 × Str)
  | [] => [x]
  | y :: r =>
    if F64.gt x.1 y.1 || (F64.eq x.1 y.1 && decide (y.2 < x.2)) then x :: y :: r
    else y :: insertBest x r

/-- The `for x in possibilities` of `get_close_matches`, `Lib/difflib.py:698-704`. -/
def closeLoop (cutoff : F64) (s : SMO Nat) : List Str → List (F64 × Str) → Py (List (F64 × Str))
  | [], acc => .ok acc
  | x :: r, acc =>
    let s := setSeq1O s x false
    let la := s.a.length
    let lb := s.b.length
    if F64.lt (calcRatio (min la lb) (la + lb)) cutoff then closeLoop cutoff s r acc
    else
      match quickPairO charOps s with
      | (_, .error e) => .error e
      | (s, .ok (m, l)) =>
        if F64.lt (calcRatio m l) cutoff then closeLoop cutoff s r acc
        else
          match ratioPairO charOps s with
          | .error e => .error e
          | .ok (s, m, l) =>
            let ratio := calcRatio m l
            closeLoop cutoff s r (if F64.ge ratio cutoff then acc ++ [(ratio, x)] else acc)

/-- `get_close_matches`, `Lib/difflib.py:667-708`. -/
def closeMatches (word : Str) (possibilities : List Str) (n : Int) (cutoff : F64) : Py (List Str) := do
  if !(n > 0) then throw (.valueError "~n must be > 0")
  if !(F64.le (F64.zero false) cutoff && F64.le cutoff F64.one) then throw (.valueError "~cutoff must be in [0.0, 1.0]")
  let s ← makeO charOps none [] [] true
  let (s, r) := setSeq2O charOps s word false
  r
  let acc ← closeLoop cutoff s possibilities []
  let sorted := acc.foldr insertBest []
  return (sorted.take n.toNat).map (·.2)

end PyLean.TextLibs.Difflib
