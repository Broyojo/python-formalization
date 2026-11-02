import PyLean.TextLibs.CsvModel
import PyLean.TextLibs.ReApi

/-!
Model of `csv.Sniffer.sniff`, `Lib/csv.py:241-463`, CPython 3.15.2.

The two `_guess` functions run the `re` model and count characters; the dictionaries are association
lists, in insertion order, which is what `max` and `.items()` see. The one float in the code is
`consistency`: its values are `consistencySteps`, and `divGe` compares the rounded quotient exactly,
so that no `Float` reaches a proof. `has_header` is not modelled.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

def restr1 : List Nat :=
  [40, 63, 80, 60, 100, 101, 108, 105, 109, 62, 91, 94, 92, 119, 92, 110, 34, 92, 39, 93, 41, 40, 63, 80, 60, 115, 112, 97, 99, 101, 62, 32, 63, 41, 40, 63, 80, 60, 113, 117, 111, 116, 101, 62, 91, 34, 92, 39, 93, 41, 40, 63, 58, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 123, 50, 125, 124, 40, 63, 33, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 41, 46, 41, 42, 43, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 40, 63, 80, 61, 100, 101, 108, 105, 109, 41]

def restr2 : List Nat :=
  [40, 63, 58, 94, 124, 92, 110, 41, 40, 63, 80, 60, 113, 117, 111, 116, 101, 62, 91, 34, 92, 39, 93, 41, 40, 63, 58, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 123, 50, 125, 124, 40, 63, 33, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 41, 46, 41, 42, 43, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 40, 63, 80, 60, 100, 101, 108, 105, 109, 62, 91, 94, 92, 119, 92, 110, 34, 92, 39, 93, 41, 40, 63, 80, 60, 115, 112, 97, 99, 101, 62, 32, 63, 41]

def restr3 : List Nat :=
  [40, 63, 80, 60, 100, 101, 108, 105, 109, 62, 91, 94, 92, 119, 92, 110, 34, 92, 39, 93, 41, 40, 63, 80, 60, 115, 112, 97, 99, 101, 62, 32, 63, 41, 40, 63, 80, 60, 113, 117, 111, 116, 101, 62, 91, 34, 92, 39, 93, 41, 40, 63, 58, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 123, 50, 125, 124, 40, 63, 33, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 41, 46, 41, 42, 43, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 40, 63, 58, 36, 124, 92, 110, 41]

def restr4 : List Nat :=
  [40, 63, 58, 94, 124, 92, 110, 41, 40, 63, 80, 60, 113, 117, 111, 116, 101, 62, 91, 34, 92, 39, 93, 41, 40, 63, 58, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 123, 50, 125, 124, 40, 63, 33, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 41, 46, 41, 42, 43, 40, 63, 80, 61, 113, 117, 111, 116, 101, 41, 40, 63, 58, 36, 124, 92, 110, 41]

/-- `consistency`, as a numerator over `2^53`, at each step of the loop. -/
def consistencySteps : List Nat :=
  [9007199254740992, 8917127262193582, 8827055269646172, 8736983277098762, 8646911284551352, 8556839292003942, 8466767299456532, 8376695306909122, 8286623314361712, 8196551321814302]



/-- `d[k] = d.get(k, 0) + 1`. -/
def bump {α : Type} [BEq α] : List (α × Nat) → α → List (α × Nat)
  | [], k => [(k, 1)]
  | (x, n) :: r, k => if x == k then (x, n + 1) :: r else (x, n) :: bump r k

/-- `max(d, key=d.get)`: the first of the largest. -/
def maxKey : List (List Nat × Nat) → List Nat
  | [] => []
  | x :: r => (r.foldl (fun b y => if y.2 > b.2 then y else b) x).1

/-- `key in delimiters`, for the single character the `delim` group holds. -/
def inDelims (delimiters : Option (List Nat)) (key : List Nat) : Bool :=
  match delimiters with
  | none => true
  | some ds => match key.head? with
    | some c => ds.contains c
    | none => false

/-- `m[n]` of a `findall` result: a group of the tuple, or a character when there is one group. -/
def itemAt (it : Re.FindItem) (n : Nat) : List Nat :=
  match it with
  | .tuple vs =>
    match vs.getD n (.str []) with
    | .str t => t
    | .none => []
  | .one (.str t) => t.take 1
  | .one .none => []

structure GQ where
  quotes : List (List Nat × Nat) := []
  delims : List (List Nat × Nat) := []
  spaces : Nat := 0
  deriving Repr, Inhabited

/-- The `for m in matches`, `Lib/csv.py:310-327`. `di` and `si` are `none` for the `KeyError`. -/
def tally (delimiters : Option (List Nat)) (qi : Nat) (di si : Option Nat) : List Re.FindItem → GQ → GQ
  | [], g => g
  | m :: ms, g =>
    let key := itemAt m qi
    let g := if !key.isEmpty then { g with quotes := bump g.quotes key } else g
    match di with
    | none => tally delimiters qi di si ms g
    | some d =>
      let key := itemAt m d
      let g := if !key.isEmpty && inDelims delimiters key then { g with delims := bump g.delims key } else g
      match si with
      | none => tally delimiters qi di si ms g
      | some s =>
        let g := if !(itemAt m s).isEmpty then { g with spaces := g.spaces + 1 } else g
        tally delimiters qi di si ms g

/-- `a in b`. -/
def isInfix : List Nat → List Nat → Bool
  | a, [] => a.isEmpty
  | a, b :: r => (a.isPrefixOf (b :: r)) || isInfix a r

/-- `dq_regexp`, `Lib/csv.py:346-353`. -/
def dqPattern (delim quote : List Nat) : List Nat :=
  let d := Re.escape delim
  [40, 63, 58, 40, 63, 60, 61] ++ d ++ [41, 124, 94, 41] ++
    (if delim == [32] then [] else [32, 42, 43]) ++ quote ++
    [40, 40, 63, 58] ++ quote ++ quote ++ [124, 91, 94] ++ quote ++ [93, 43, 43, 41, 42, 43, 41] ++
    quote ++ [40, 63, 58] ++ d ++ [124, 36, 41]

/-- The end of `_guess_quote_and_delimiter`, `Lib/csv.py:329-358`. -/
def gqFinish (data : List Nat) (g : GQ) : Py (List Nat × Bool × List Nat × Bool) := do
  let quotechar := maxKey g.quotes
  let (delim, skip) :=
    if !g.delims.isEmpty then
      let d := maxKey g.delims
      let n := (g.delims.lookup d).getD 0
      (if d == [10] then [] else d, n == g.spaces)
    else (([] : List Nat), false)
  let dq ←
    if !delim.isEmpty then do
      let p ← Re.compilePat true (dqPattern delim quotechar) 8
      let ms ← Re.scanAll p data 0 data.length true
      pure (ms.any fun m =>
        match Re.matchSlice data m 1 with
        | .str t => isInfix (quotechar ++ quotechar) t
        | .none => false)
    else pure false
  return (quotechar, dq, delim, skip)

/-- `_guess_quote_and_delimiter`, `Lib/csv.py:276-358`: the first regexp that finds anything. -/
def guessQuote (data : List Nat) (delimiters : Option (List Nat)) :
    Py (List Nat × Bool × List Nat × Bool) := do
  let rec go : List (List Nat × Nat × Option Nat × Option Nat) → Py (List Nat × Bool × List Nat × Bool)
    | [] => .ok ([], false, [], false)
    | (r, qi, di, si) :: rest => do
      let p ← Re.compilePat true r (16 ||| 8)
      let ms ← Re.findall p data 0 data.length
      if ms.isEmpty then go rest
      else gqFinish data (tally delimiters qi di si ms {})
  go [(restr1, 2, some 0, some 1), (restr2, 0, some 1, some 2), (restr3, 2, some 0, some 1),
    (restr4, 0, none, none)]

/-- `data.split('\n')`. -/
def splitNL : List Nat → List (List Nat)
  | [] => [[]]
  | c :: r =>
    let rest := splitNL r
    if c == 10 then [] :: rest
    else match rest with
      | h :: t => (c :: h) :: t
      | [] => [[c]]

/-- `d[k] = v`, keeping `k` where it is. -/
def setKey {β : Type} : List (Nat × β) → Nat → β → List (Nat × β)
  | [], k, v => [(k, v)]
  | (x, w) :: r, k, v => if x == k then (x, v) :: r else (x, w) :: setKey r k v

/-- `line.count(char)`. -/
def count1 (line : List Nat) (c : Nat) : Nat := (line.filter (· == c)).length

/-- `line.count("%c " % d)`: not overlapping. -/
def countPair (d : Nat) : List Nat → Nat
  | a :: b :: r => if a == d && b == 32 then countPair d r + 1 else countPair d (b :: r)
  | _ => 0
termination_by l => l.length

/-- `Counter(line).items()`: the characters in the order they first appear. -/
def counterOf : List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], acc => acc
  | c :: r, acc =>
    match acc.lookup c with
    | some n => counterOf r (setKey acc c (n + 1))
    | none => counterOf r (acc ++ [(c, 1)])

/-- `char_frequency[char][count] += 1`: a new character goes last, as in a `defaultdict`. -/
def bumpChar : List (Nat × List (Nat × Nat)) → Nat → Nat → List (Nat × List (Nat × Nat))
  | [], c, n => [(c, bump [] n)]
  | (x, w) :: r, c, n => if x == c then (x, bump w n) :: r else (x, w) :: bumpChar r c n

/-- `Lib/csv.py:395-398`, for one line. -/
def addLine (cf : List (Nat × List (Nat × Nat))) (line : List Nat) : List (Nat × List (Nat × Nat)) :=
  (counterOf line []).foldl (fun cf x => if x.1 < 128 then bumpChar cf x.1 x.2 else cf) cf

/-- `max(items, key=lambda x: x[1])`: the first of the largest. -/
def maxItem : List (Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | x :: r => r.foldl (fun b y => if y.2 > b.2 then y else b) x

/-- `modes[char]`, `Lib/csv.py:406-414`, or `none` for the `continue`. -/
def modeOf (items : List (Nat × Nat)) : Option (Nat × Int) :=
  match items with
  | [] => none
  | [(f, n)] => if f == 0 then none else some (f, n)
  | _ =>
    let b := maxItem items
    let rest := items.erase b
    some (b.1, (b.2 : Int) - ((rest.map (·.2)).foldl (· + ·) 0 : Nat))

/-- `items`, with the lines a character is missing from, `Lib/csv.py:400-404`. -/
def itemsOf (numLines : Nat) (counts : List (Nat × Nat)) : List (Nat × Nat) :=
  let missed := numLines - (counts.map (·.2)).foldl (· + ·) 0
  if missed ≠ 0 then counts ++ [(0, missed)] else counts

/-- The `for char, counts in char_frequency.items()`, `Lib/csv.py:399-414`. -/
def updateModes (numLines : Nat) (modes : List (Nat × (Nat × Int))) :
    List (Nat × List (Nat × Nat)) → List (Nat × (Nat × Int))
  | [] => modes
  | (c, counts) :: r =>
    match modeOf (itemsOf numLines counts) with
    | none => updateModes numLines modes r
    | some v => updateModes numLines (setKey modes c v) r

/-- `(v / total) >= c`, where `/` rounds to a double and `c` is `C / 2^53`, in `[0.9, 1]`. A quotient
below one half rounds below `c`, and from one half up the doubles are multiples of `2^-53`. -/
def divGe (v t C : Nat) : Bool :=
  if v ≥ t then true
  else if 2 * v < t then false
  else
    let n := v * 2 ^ 53
    let q := n / t
    let r := n % t
    let up := 2 * r > t || (2 * r == t && q % 2 == 1)
    (if up then q + 1 else q) ≥ C

/-- `delimiters is None or k in delimiters`, for a character. -/
def allowed (delimiters : Option (List Nat)) (k : Nat) : Bool :=
  match delimiters with
  | none => true
  | some ds => ds.contains k

/-- The `for k, v in modeList`, `Lib/csv.py:427-431`. -/
def scanModes (delimiters : Option (List Nat)) (total C : Nat) :
    List (Nat × (Nat × Int)) → List (Nat × (Nat × Int)) → List (Nat × (Nat × Int))
  | [], d => d
  | (k, v) :: r, d =>
    let keep := decide (v.1 > 0) && decide (v.2 > 0) && divGe v.2.toNat total C && allowed delimiters k
    scanModes delimiters total C r (if keep then setKey d k v else d)

/-- The `while len(delims) == 0 and consistency >= threshold`, `Lib/csv.py:426-432`. -/
def consistencyLoop (delimiters : Option (List Nat)) (total : Nat) (modes : List (Nat × (Nat × Int))) :
    List Nat → List (Nat × (Nat × Int)) → List (Nat × (Nat × Int))
  | [], d => d
  | c :: cs, d =>
    if d.isEmpty then consistencyLoop delimiters total modes cs (scanModes delimiters total c modes d)
    else d

/-- `skipinitialspace` of a delimiter. -/
def skipOf (data : List (List Nat)) (d : Nat) : Bool :=
  let l := data.headD []
  count1 l d == countPair d l

/-- The `while start < len(data)`, `Lib/csv.py:392-442`. `.inl` is a return from inside it. -/
def gdLoop (delimiters : Option (List Nat)) (data : List (List Nat)) (chunk : Nat) :
    (fuel iteration numLines start stop : Nat) → List (Nat × List (Nat × Nat)) → List (Nat × (Nat × Int)) →
    List (Nat × (Nat × Int)) → Sum (Nat × Bool) (List (Nat × (Nat × Int)))
  | 0, _, _, _, _, _, _, d => .inr d
  | fuel + 1, iteration, numLines, start, stop, cf, modes, d =>
    if start < data.length then
      let iteration := iteration + 1
      let lines := (data.drop start).take (stop - start)
      let numLines := numLines + lines.length
      let cf := lines.foldl addLine cf
      let modes := updateModes numLines modes cf
      let total := min (chunk * iteration) data.length
      let d := consistencyLoop delimiters total modes consistencySteps d
      match d with
      | [(k, _)] => .inl (k, skipOf data k)
      | _ => gdLoop delimiters data chunk fuel iteration numLines stop (stop + chunk) cf modes d
    else .inr d

def preferred : List Nat := [44, 9, 59, 32, 58]

/-- `items.sort(); items[-1][1]`: the last of `((v0, v1), k)`, in that order. -/
def lastItem : List (Nat × (Nat × Int)) → Nat
  | [] => 0
  | x :: r =>
    (r.foldl (fun b y =>
      if decide (y.2.1 > b.2.1) || (decide (y.2.1 == b.2.1) && (decide (y.2.2 > b.2.2) ||
          (decide (y.2.2 == b.2.2) && decide (y.1 > b.1)))) then y else b) x).1

/-- `_guess_delimiter`, `Lib/csv.py:361-463`: the delimiter, `[]` for `''`, and `skipinitialspace`. -/
def guessDelimiter (sample : List Nat) (delimiters : Option (List Nat)) : List Nat × Bool :=
  let data := (splitNL sample).filter (!·.isEmpty)
  let chunk := min 10 data.length
  match gdLoop delimiters data chunk (data.length + 1) 0 0 0 chunk [] [] [] with
  | .inl (k, s) => ([k], s)
  | .inr d =>
    if d.isEmpty then ([], false)
    else
      let hit := if d.length > 1 then preferred.find? (fun p => d.any (·.1 == p)) else none
      match hit with
      | some p => ([p], skipOf data p)
      | none =>
        let k := lastItem d
        ([k], skipOf data k)

/-- `sample.replace('\r\n', '\n')`. -/
def crlf : List Nat → List Nat
  | 13 :: 10 :: r => 10 :: crlf r
  | c :: r => c :: crlf r
  | [] => []
termination_by l => l.length

/-- What `sniff` gives: the attributes of the `dialect` class. -/
structure Sniffed where
  delimiter : List Nat
  quotechar : List Nat
  doublequote : Bool
  skipinitialspace : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `Sniffer.sniff`, `Lib/csv.py:241-273`. -/
def sniff (sample : List Nat) (delimiters : Option (List Nat)) : Py Sniffed := do
  let sample := (crlf sample).map fun c => if c == 13 then 10 else c
  let (q, dq, d, skip) ← guessQuote sample delimiters
  let (d, skip) := if d.isEmpty then guessDelimiter sample delimiters else (d, skip)
  if d.isEmpty then throw (csvErr "Could not determine delimiter")
  return ⟨d, if q.isEmpty then [34] else q, dq, skip⟩

end PyLean.TextLibs.Csv
