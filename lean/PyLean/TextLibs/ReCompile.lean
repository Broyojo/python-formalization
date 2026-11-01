import PyLean.TextLibs.ReParse
import PyLean.TextLibs.ReCasefix
import PyLean.UnicodeObj.Ctype

/-!
Model of `Lib/re/_compiler.py`, CPython 3.14.7. The output is the list of code words, and the
difftest compares it with `re._compiler._code` word for word. `code[skip] = len(code) - skip` is
computed from fragment lengths instead of patching a list.
-/

namespace PyLean.TextLibs.Re

open PyLean

/-! ### Constants, `Lib/re/_constants.py:78-153` -/

def OP_FAILURE : Nat := 0
def OP_SUCCESS : Nat := 1
def OP_ANY : Nat := 2
def OP_ANY_ALL : Nat := 3
def OP_ASSERT : Nat := 4
def OP_ASSERT_NOT : Nat := 5
def OP_AT : Nat := 6
def OP_BRANCH : Nat := 7
def OP_CATEGORY : Nat := 8
def OP_CHARSET : Nat := 9
def OP_BIGCHARSET : Nat := 10
def OP_GROUPREF : Nat := 11
def OP_GROUPREF_EXISTS : Nat := 12
def OP_IN : Nat := 13
def OP_INFO : Nat := 14
def OP_JUMP : Nat := 15
def OP_LITERAL : Nat := 16
def OP_MARK : Nat := 17
def OP_MAX_UNTIL : Nat := 18
def OP_MIN_UNTIL : Nat := 19
def OP_NOT_LITERAL : Nat := 20
def OP_NEGATE : Nat := 21
def OP_RANGE : Nat := 22
def OP_REPEAT : Nat := 23
def OP_REPEAT_ONE : Nat := 24
def OP_MIN_REPEAT_ONE : Nat := 26
def OP_ATOMIC_GROUP : Nat := 27
def OP_POSSESSIVE_REPEAT : Nat := 28
def OP_POSSESSIVE_REPEAT_ONE : Nat := 29
def OP_GROUPREF_IGNORE : Nat := 30
def OP_IN_IGNORE : Nat := 31
def OP_LITERAL_IGNORE : Nat := 32
def OP_NOT_LITERAL_IGNORE : Nat := 33
def OP_GROUPREF_LOC_IGNORE : Nat := 34
def OP_IN_LOC_IGNORE : Nat := 35
def OP_LITERAL_LOC_IGNORE : Nat := 36
def OP_NOT_LITERAL_LOC_IGNORE : Nat := 37
def OP_GROUPREF_UNI_IGNORE : Nat := 38
def OP_IN_UNI_IGNORE : Nat := 39
def OP_LITERAL_UNI_IGNORE : Nat := 40
def OP_NOT_LITERAL_UNI_IGNORE : Nat := 41
def OP_RANGE_UNI_IGNORE : Nat := 42

def MAXCODE : Nat := 2 ^ 32 - 1

/-- `_sre.ascii_iscased`, `Modules/_sre/sre.c:436-437`. -/
def asciiIscased (c : Nat) : Bool := c < 128 && isLetter c

/-- `sre_lower_ascii`, `Modules/_sre/sre.c:143-146`. -/
def lowerAscii (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `sre_lower_unicode`, `Modules/_sre/sre.c:172-175`. -/
def lowerUnicode (c : Nat) : Nat := PyLean.UnicodeObj.toLowercase c

/-- `sre_upper_unicode`, `Modules/_sre/sre.c:177-180`. -/
def upperUnicode (c : Nat) : Nat := PyLean.UnicodeObj.toUppercase c

/-- `_sre.unicode_iscased`, `Modules/_sre/sre.c:452-453`. -/
def unicodeIscased (c : Nat) : Bool := c != lowerUnicode c || c != upperUnicode c

/-- The `iscased`, `tolower`, `fixes` triple of `_compile`, `Lib/re/_compiler.py:47-57`. -/
structure CaseFns where
  iscased : Nat → Bool
  tolower : Nat → Nat
  fixes : List (Nat × List Nat)

def hasFlag (flags f : Nat) : Bool := (flags &&& f) != 0

def caseFor (flags : Nat) : Option CaseFns :=
  if hasFlag flags FLAG_IGNORECASE && !hasFlag flags FLAG_LOCALE then
    if hasFlag flags FLAG_UNICODE then some ⟨unicodeIscased, lowerUnicode, extraCases⟩
    else some ⟨asciiIscased, lowerAscii, []⟩
  else none

/-- `_get_iscased`, `Lib/re/_compiler.py:442-448`. -/
def getIscased (flags : Nat) : Option (Nat → Bool) :=
  if !hasFlag flags FLAG_IGNORECASE then none
  else if hasFlag flags FLAG_UNICODE then some unicodeIscased
  else some asciiIscased

/-- `_combine_flags`, `Lib/re/_compiler.py:33-37`. -/
def combineFlags (flags add del : Nat) : Nat :=
  let f := if (add &&& TYPE_FLAGS) ≠ 0 then flags &&& (2 ^ 16 - 1 - TYPE_FLAGS) else flags
  (f ||| add) &&& (2 ^ 16 - 1 - del)

/-! ### `_optimize_charset`, `Lib/re/_compiler.py:248-395` -/

/-- A compiled charset item. -/
inductive CItem where
  | lit (c : Nat)
  | rng (lo hi : Nat)
  | rngUni (lo hi : Nat)
  | cat (c : Cat)
  | neg
  | charset (data : List Nat)
  | big (data : List Nat)
  deriving Repr, DecidableEq, Inhabited

def ofSetItem : SetItem → CItem
  | .literal c => .lit c
  | .range a b => .rng a b
  | .category c => .cat c
  | .negate => .neg

/-- `CH_NEGATE`, `Lib/re/_constants.py:209`. -/
def chNegate : Cat → Cat
  | .digit => .notDigit | .notDigit => .digit
  | .space => .notSpace | .notSpace => .space
  | .word => .notWord | .notWord => .word

structure OSt where
  out : List CItem := []
  tail : List CItem := []
  cm : Array Bool := Array.replicate 256 false
  cased : Bool := false
  deriving Repr, Inhabited

/-- `charmap[i] = 1`, with `none` for the `IndexError`. -/
def cmSet (cm : Array Bool) (i : Nat) : Option (Array Bool) :=
  if i < cm.size then some (cm.set! i true) else none

/-- `charmap[k] = 1` for each `k`: the map as far as it got, and whether an `IndexError` hit. -/
def cmSetAll (cm : Array Bool) : List Nat → Array Bool × Bool
  | [] => (cm, false)
  | k :: ks =>
    match cmSet cm k with
    | none => (cm, true)
    | some c => cmSetAll c ks

/-- The body of the `try` for one literal, `Lib/re/_compiler.py:257-267`: the new state, `av`, and
whether an `IndexError` hit. -/
def literalPass (f : Option CaseFns) (st : OSt) (av : Nat) : OSt × Nat × Bool :=
  match f with
  | none =>
    match cmSet st.cm av with
    | none => (st, av, true)
    | some c => ({ st with cm := c }, av, false)
  | some cf =>
    let av := cf.tolower av
    match cmSet st.cm av with
    | none => (st, av, true)
    | some c =>
      let (c, err) := cmSetAll c ((cf.fixes.lookup av).getD [])
      if err then ({ st with cm := c }, av, true)
      else ({ st with cm := c, cased := st.cased || cf.iscased av }, av, false)

/-- The loop body over `range(av[0], av[1]+1)`, `Lib/re/_compiler.py:269-284`. -/
def rangeMark (f : Option CaseFns) : (n : Nat) → (i : Nat) → Array Bool → Array Bool × Bool
  | 0, _, cm => (cm, false)
  | n + 1, i, cm =>
    match f with
    | none =>
      match cmSet cm i with
      | none => (cm, true)
      | some c => rangeMark f n (i + 1) c
    | some cf =>
      let j := cf.tolower i
      match cmSet cm j with
      | none => (cm, true)
      | some c =>
        let (c, err) := cmSetAll c ((cf.fixes.lookup j).getD [])
        if err then (c, true) else rangeMark f n (i + 1) c

def anyRange (p : Nat → Bool) : (n i : Nat) → Bool
  | 0, _ => false
  | n + 1, i => p i || anyRange p n (i + 1)

/-- `charmap += b'\0' * 0xff00`. -/
def widen (st : OSt) : OSt := { st with cm := st.cm ++ Array.replicate 0xff00 false }

/-- The `while True` for a literal, with its `except IndexError`, `:293-320`. -/
def doLiteral (f : Option CaseFns) (st0 : OSt) (av0 : Nat) : OSt :=
  let (st, av, err) := literalPass f st0 av0
  if !err then st
  else
    let finish (st : OSt) (av : Nat) : OSt :=
      let cased := match f with
        | some cf => st.cased || cf.iscased av
        | none => st.cased
      { st with cased, tail := st.tail ++ [.lit av] }
    if st.cm.size == 256 then
      let (st, av, err) := literalPass f (widen st) av
      if !err then st else finish st av
    else finish st av

/-- The same for a range. -/
def doRange (f : Option CaseFns) (st0 : OSt) (lo hi : Nat) : OSt :=
  let n := hi + 1 - lo
  let attempt (st : OSt) : OSt × Bool :=
    let (cm, err) := rangeMark f n lo st.cm
    let st := { st with cm }
    if err then (st, true)
    else match f with
      | some cf =>
        (if st.cased then st else { st with cased := anyRange cf.iscased n lo }, false)
      | none => (st, false)
  let finish (st : OSt) : OSt :=
    match f with
    | some cf =>
      { st with cased := true, tail := st.tail ++ [if cf.fixes.isEmpty then .rng lo hi else .rngUni lo hi] }
    | none => { st with tail := st.tail ++ [.rng lo hi] }
  let (st, err) := attempt st0
  if !err then st
  else if st.cm.size == 256 then
    let (st, err) := attempt (widen st)
    if !err then st else finish st
  else finish st

/-- `charmap.find(v, q)`, or `none` for `-1`. -/
def cmFind (cm : Array Bool) (v : Bool) : (fuel q : Nat) → Option Nat
  | 0, _ => none
  | fuel + 1, q =>
    if q ≥ cm.size then none
    else if cm[q]! == v then some q
    else cmFind cm v fuel (q + 1)

/-- The `# compress character map` loop, `:323-336`: `none` for `runs = None`. -/
def cmRuns (cm : Array Bool) : (fuel : Nat) → List (Nat × Nat) → Nat → Option (List (Nat × Nat))
  | 0, runs, _ => some runs
  | fuel + 1, runs, q =>
    match cmFind cm true cm.size q with
    | none => some runs
    | some p =>
      if runs.length ≥ 2 then none
      else
        match cmFind cm false cm.size p with
        | none => some (runs ++ [(p, cm.size)])
        | some q => cmRuns cm fuel (runs ++ [(p, q)]) q

/-- `_mk_bitmap`, `Lib/re/_compiler.py:400-403`: 32-bit words, low bit first. -/
def mkBitmap (bits : List Bool) : List Nat :=
  let rec go : (fuel : Nat) → List Bool → List Nat
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, b =>
      ((b.take 32).foldr (fun x acc => acc * 2 + (if x then 1 else 0)) 0) :: go fuel (b.drop 32)
  go bits.length bits

/-- `_bytes_to_codes`, `Lib/re/_compiler.py:405-410`: little-endian 32-bit words. -/
def bytesToCodes (b : List Nat) : List Nat :=
  let rec go : (fuel : Nat) → List Nat → List Nat
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, s =>
      ((s.take 4).foldr (fun x acc => acc * 256 + x) 0) :: go fuel (s.drop 4)
  go b.length b

/-- The chunking of a big charset, `:378-392`. -/
def bigCharset (cm : Array Bool) : List Nat :=
  let bits := cm.toList
  let rec go2 : (i : Nat) → List Bool → List (List Bool × Nat) → List Nat → Nat → List Bool →
      Nat × List Nat × List Bool
    | 0, _, _, mapping, block, data => (block, mapping.reverse, data)
    | i + 1, rest, comps, mapping, block, data =>
      let chunk := rest.take 256
      match comps.lookup chunk with
      | some b => go2 i (rest.drop 256) comps (b :: mapping) block data
      | none => go2 i (rest.drop 256) ((chunk, block) :: comps) (block :: mapping) (block + 1) (data ++ chunk)
  let (block, mapping, data) := go2 256 bits [] [] 0 []
  block :: bytesToCodes mapping ++ mkBitmap data

/-- The `for op, av in charset` loop, `:254-320`. `.inl` is the early return for `[\s\S]`. -/
def optLoop (f : Option CaseFns) : List CItem → OSt → Sum (List CItem) OSt
  | [], st => .inr st
  | it :: rest, st =>
    match it with
    | .lit av => optLoop f rest (doLiteral f st av)
    | .rng lo hi => optLoop f rest (doRange f st lo hi)
    | .neg => optLoop f rest { st with out := st.out ++ [.neg] }
    | .cat c =>
      if !st.tail.isEmpty ∧ (CItem.cat (chNegate c)) ∈ st.tail then
        .inl (if st.out.isEmpty then [.neg] else [])
      else optLoop f rest { st with tail := st.tail ++ [it] }
    | _ => optLoop f rest { st with tail := st.tail ++ [it] }

/-- `_optimize_charset`, `Lib/re/_compiler.py:248-395`. -/
def optimizeCharset (charset : List CItem) (f : Option CaseFns) : List CItem × Bool :=
  match optLoop f charset {} with
  | .inl out => (out, false)
  | .inr st =>
    match cmRuns st.cm 3 [] 0 with
    | some runs =>
      let out := st.out ++ runs.map (fun r => if r.2 - r.1 == 1 then .lit r.1 else .rng r.1 (r.2 - 1)) ++ st.tail
      if st.cased ∨ out.length < charset.length then (out, st.cased) else (charset, st.cased)
    | none =>
      if st.cm.size == 256 then
        (st.out ++ [.charset (mkBitmap st.cm.toList)] ++ st.tail, st.cased)
      else (st.out ++ [.big (bigCharset st.cm)] ++ st.tail, st.cased)

/-- `CH_LOCALE` and `CH_UNICODE`, `Lib/re/_constants.py:187-207`, on the parser's categories. -/
def catCode (flags : Nat) (c : Cat) : Nat :=
  let base : Nat := match c with
    | .digit => 0 | .notDigit => 1 | .space => 2 | .notSpace => 3 | .word => 4 | .notWord => 5
  if hasFlag flags FLAG_LOCALE then
    if base == 4 then 8 else if base == 5 then 9 else base
  else if hasFlag flags FLAG_UNICODE then base + 10
  else base

/-- `_compile_charset`, `Lib/re/_compiler.py:221-246`. -/
def compileCharset (charset : List CItem) (flags : Nat) : List Nat :=
  (charset.flatMap fun it =>
    match it with
    | .neg => [OP_NEGATE]
    | .lit c => [OP_LITERAL, c]
    | .rng a b => [OP_RANGE, a, b]
    | .rngUni a b => [OP_RANGE_UNI_IGNORE, a, b]
    | .charset d => OP_CHARSET :: d
    | .big d => OP_BIGCHARSET :: d
    | .cat c => [OP_CATEGORY, catCode flags c]) ++ [OP_FAILURE]

/-! ### `_compile`, `Lib/re/_compiler.py:39-219` -/

/-- `_simple`, `Lib/re/_compiler.py:412-419`. -/
def simple : List Node → Bool
  | [.literal _] | [.notLiteral _] | [.any] | [.in_ _] => true
  | [.subpattern none _ _ p] => simple p
  | _ => false

/-- The `op in LITERAL_CODES` branch, `Lib/re/_compiler.py:59-86`. `isNot` is `NOT_LITERAL`. -/
def compLiteral (flags : Nat) (isNot : Bool) (av : Nat) : List Nat :=
  let op := if isNot then OP_NOT_LITERAL else OP_LITERAL
  if !hasFlag flags FLAG_IGNORECASE then [op, av]
  else if hasFlag flags FLAG_LOCALE then
    [if isNot then OP_NOT_LITERAL_LOC_IGNORE else OP_LITERAL_LOC_IGNORE, av]
  else
    match caseFor flags with
    | none => [op, av]
    | some cf =>
      if !cf.iscased av then [op, av]
      else
        let lo := cf.tolower av
        if cf.fixes.isEmpty then [if isNot then OP_NOT_LITERAL_IGNORE else OP_LITERAL_IGNORE, lo]
        else
          match cf.fixes.lookup lo with
          | none => [if isNot then OP_NOT_LITERAL_UNI_IGNORE else OP_LITERAL_UNI_IGNORE, lo]
          | some extra =>
            let body := (if isNot then [OP_NEGATE] else []) ++
              (lo :: extra).flatMap (fun k => [OP_LITERAL, k]) ++ [OP_FAILURE]
            OP_IN_UNI_IGNORE :: (body.length + 1) :: body

/-- The `op is IN` branch, `Lib/re/_compiler.py:87-104`. -/
def compIn (flags : Nat) (av : List SetItem) : List Nat :=
  let f := caseFor flags
  let (charset, hascased) := optimizeCharset (av.map ofSetItem) f
  if charset.isEmpty then [OP_FAILURE]
  else if charset == [.neg] then [OP_ANY_ALL]
  else
    let op :=
      if hasFlag flags FLAG_IGNORECASE && hasFlag flags FLAG_LOCALE then OP_IN_LOC_IGNORE
      else if !hascased then OP_IN
      else match f with
        | some cf => if cf.fixes.isEmpty then OP_IN_IGNORE else OP_IN_UNI_IGNORE
        | none => OP_IN_IGNORE
    let body := compileCharset charset flags
    op :: (body.length + 1) :: body

/-- `AT` codes after `AT_MULTILINE`, `AT_LOCALE` and `AT_UNICODE`. -/
def atCode (flags : Nat) (a : AtCode) : Nat :=
  let multi := hasFlag flags FLAG_MULTILINE
  let loc := hasFlag flags FLAG_LOCALE
  let uni := hasFlag flags FLAG_UNICODE
  match a with
  | .beginning => if multi then 1 else 0
  | .beginningString => 2
  | .boundary => if loc then 8 else if uni then 10 else 3
  | .nonBoundary => if loc then 9 else if uni then 11 else 4
  | .end_ => if multi then 6 else 5
  | .endString => 7

mutual
  def compNode (gw : List (Option (Nat × Nat))) (flags : Nat) : Node → Py (List Nat)
    | .literal c => .ok (compLiteral flags false c)
    | .notLiteral c => .ok (compLiteral flags true c)
    | .in_ s => .ok (compIn flags s)
    | .any => .ok [if hasFlag flags FLAG_DOTALL then OP_ANY_ALL else OP_ANY]
    | .repeat_ k mn mx p => do
      let (op0, op1, op2) : Nat × Nat × Nat := match k with
        | .min => (OP_REPEAT, OP_MIN_UNTIL, OP_MIN_REPEAT_ONE)
        | .max => (OP_REPEAT, OP_MAX_UNTIL, OP_REPEAT_ONE)
        | .possessive => (OP_POSSESSIVE_REPEAT, OP_SUCCESS, OP_POSSESSIVE_REPEAT_ONE)
      let c ← compList gw flags p
      if simple p then
        return [op2, c.length + 5 - 1, mn, mx] ++ c ++ [OP_SUCCESS]
      else
        return [op0, c.length + 4 - 1, mn, mx] ++ c ++ [op1]
    | .subpattern g add del p => do
      let c ← compList gw (combineFlags flags add del) p
      match g with
      | some gid =>
        if gid ≠ 0 then
          return [OP_MARK, (gid - 1) * 2] ++ c ++ [OP_MARK, (gid - 1) * 2 + 1]
        else return c
      | none => return c
    | .atomic p => do
      let c ← compList gw flags p
      return [OP_ATOMIC_GROUP, c.length + 2] ++ c ++ [OP_SUCCESS]
    | .failure => .ok [OP_FAILURE]
    | .assert_ d p => compAssert gw flags OP_ASSERT d p
    | .assertNot d p => compAssert gw flags OP_ASSERT_NOT d p
    | .at_ a => .ok [OP_AT, atCode flags a]
    | .branch alts => do
      let frags ← compAlts gw flags alts
      return OP_BRANCH :: frags
    | .groupref g =>
      let op :=
        if !hasFlag flags FLAG_IGNORECASE then OP_GROUPREF
        else if hasFlag flags FLAG_LOCALE then OP_GROUPREF_LOC_IGNORE
        else match caseFor flags with
          | some cf => if cf.fixes.isEmpty then OP_GROUPREF_IGNORE else OP_GROUPREF_UNI_IGNORE
          | none => OP_GROUPREF_IGNORE
      .ok [op, g - 1]
    | .grouprefExists g yes no => do
      let y ← compList gw flags yes
      match no with
      | some (n :: ns) =>
        let c ← compList gw flags (n :: ns)
        return [OP_GROUPREF_EXISTS, g - 1, y.length + 3 + 1 - 0] ++ y ++ [OP_JUMP, c.length + 1] ++ c
      | _ => return [OP_GROUPREF_EXISTS, g - 1, y.length + 2] ++ y

  /-- The `op in ASSERT_CODES` branch, `Lib/re/_compiler.py:150-164`. -/
  def compAssert (gw : List (Option (Nat × Nat))) (flags op : Nat) (d : Int) (p : List Node) :
      Py (List Nat) := do
    let back ←
      if d ≥ 0 then pure 0
      else
        let (lo, hi) := getwidth gw p
        if lo > MAXCODE then
          (Except.error (.named "PatternError" "looks too much behind") : Py Nat)
        else if lo ≠ hi then
          Except.error (.named "PatternError" "look-behind requires fixed-width pattern")
        else pure lo
    let c ← compList gw flags p
    return [op, c.length + 3, back] ++ c ++ [OP_SUCCESS]

  def compList (gw : List (Option (Nat × Nat))) (flags : Nat) : List Node → Py (List Nat)
    | [] => .ok []
    | n :: ns => do
      let a ← compNode gw flags n
      let b ← compList gw flags ns
      return a ++ b

  /-- The alternatives of `BRANCH`, `Lib/re/_compiler.py:174-187`, ending with the `FAILURE` that
  each `JUMP` skips to. -/
  def compAlts (gw : List (Option (Nat × Nat))) (flags : Nat) : List (List Node) → Py (List Nat)
    | [] => .ok [OP_FAILURE]
    | a :: as => do
      let c ← compList gw flags a
      let rest ← compAlts gw flags as
      return [c.length + 3] ++ c ++ [OP_JUMP, rest.length + 1] ++ rest
end

/-! ### `_compile_info`, `Lib/re/_compiler.py:421-585` -/

/-- `_generate_overlap_table`, `Lib/re/_compiler.py:421-440`. -/
def overlapTable (pfx : List Nat) : List Nat :=
  let at_ (i : Nat) := pfx.getD i 0
  let rec walk (i : Nat) (table : List Nat) : (fuel idx : Nat) → Nat
    | 0, _ => 0
    | fuel + 1, idx =>
      if at_ i == at_ idx then idx + 1
      else if idx == 0 then 0
      else walk i table fuel (table.getD (idx - 1) 0)
  let rec go : (fuel i : Nat) → List Nat → List Nat
    | 0, _, table => table
    | fuel + 1, i, table =>
      go fuel (i + 1) (table ++ [walk i table (i + 1) (table.getD (i - 1) 0)])
  match pfx with
  | [] => []
  | _ => go (pfx.length - 1) 1 [0]

/-- `_get_literal_prefix`, `Lib/re/_compiler.py:450-479`: prefix, `prefix_skip`, `got_all`. -/
def literalPrefix : (fuel : Nat) → List Node → Nat → List Nat → Option Nat → List Nat × Option Nat × Bool
  | 0, _, _, pfx, skip => (pfx, skip, false)
  | _ + 1, [], _, pfx, skip => (pfx, skip, true)
  | fuel + 1, n :: ns, flags, pfx, skip =>
    let iscased := getIscased flags
    match n with
    | .literal av =>
      match iscased with
      | some f => if f av then (pfx, skip, false) else literalPrefix fuel ns flags (pfx ++ [av]) skip
      | none => literalPrefix fuel ns flags (pfx ++ [av]) skip
    | .subpattern group add del p =>
      let flags1 := combineFlags flags add del
      if hasFlag flags1 FLAG_IGNORECASE && hasFlag flags1 FLAG_LOCALE then (pfx, skip, false)
      else
        let (p1, s1, gotAll) := literalPrefix fuel p flags1 [] none
        let skip' := match skip with
          | some x => some x
          | none =>
            if group.isSome then some pfx.length
            else s1.map (pfx.length + ·)
        if gotAll then literalPrefix fuel ns flags (pfx ++ p1) skip'
        else (pfx ++ p1, skip', false)
    | _ => (pfx, skip, false)

/-- `any(map(iscased, range(a, b+1)))`. -/
def rangeCased (f : Nat → Bool) (a b : Nat) : Bool := anyRange f (b + 1 - a) a

/-- `_get_charset_prefix`, `Lib/re/_compiler.py:481-523`. -/
def charsetPrefix : (fuel : Nat) → List Node → Nat → Option (List SetItem)
  | 0, _, _ => none
  | fuel + 1, p, flags =>
    match p with
    | [] => none
    | .subpattern _ add del q :: _ =>
      let flags := combineFlags flags add del
      if hasFlag flags FLAG_IGNORECASE && hasFlag flags FLAG_LOCALE then none
      else charsetPrefix fuel q flags
    | n :: _ =>
      let iscased := getIscased flags
      let cased (c : Nat) : Bool := match iscased with
        | some f => f c
        | none => false
      match n with
      | .literal av => if cased av then none else some [.literal av]
      | .branch alts =>
        let rec go : List (List Node) → List SetItem → Option (List SetItem)
          | [], acc => some acc
          | a :: as, acc =>
            match a with
            | .literal av :: _ => if cased av then none else go as (acc ++ [.literal av])
            | _ => none
        go alts []
      | .in_ charset =>
        match iscased with
        | none => some charset
        | some f =>
          let bad := charset.any fun it =>
            match it with
            | .literal c => f c
            | .range a b => b > 0xffff || rangeCased f a b
            | _ => false
          if bad then none else some charset
      | _ => none

/-- `_compile_info`, `Lib/re/_compiler.py:525-585`. -/
def compileInfo (gw : List (Option (Nat × Nat))) (p : List Node) (flags : Nat) : List Nat :=
  let (lo, hi0) := getwidth gw p
  let hi := if hi0 > MAXCODE then MAXCODE else hi0
  if lo = 0 then [OP_INFO, 4, 0, lo, hi]
  else
    let locIgnore := hasFlag flags FLAG_IGNORECASE && hasFlag flags FLAG_LOCALE
    let (pfx, skip, gotAll) :=
      if locIgnore then (([] : List Nat), some 0, false) else literalPrefix (p.length + 64) p flags [] none
    let charset : List CItem :=
      if locIgnore || !pfx.isEmpty then []
      else
        match charsetPrefix 64 p flags with
        | some cs =>
          let c := (optimizeCharset (cs.map ofSetItem) none).1
          if c == [.neg] then [] else c
        | none => []
    let mask : Nat :=
      if !pfx.isEmpty then (if skip.isNone && gotAll then 3 else 1)
      else if !charset.isEmpty then 4 else 0
    let tailWords :=
      if !pfx.isEmpty then
        [pfx.length, skip.getD pfx.length] ++ pfx ++ overlapTable pfx
      else if !charset.isEmpty then compileCharset charset flags
      else []
    let (loWord, _) := if lo < MAXCODE then (lo, 0) else (MAXCODE, 0)
    let body := [mask, loWord, hi] ++ tailWords
    OP_INFO :: (body.length + 1) :: body

/-- `_code`, `Lib/re/_compiler.py:590-603`. -/
def codeOf (p : Parsed) (flags : Nat) : Py (List Nat) := do
  let fl := p.flags ||| flags
  let c ← compList p.groupwidths fl p.p
  return compileInfo p.groupwidths p.p fl ++ c ++ [OP_SUCCESS]

end PyLean.TextLibs.Re
