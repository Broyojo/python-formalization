import PyLean.TextLibs.ReEngine
import PyLean.UnicodeObj.Repr

/-!
The Python-facing layer of `Modules/_sre/sre.c` and `Lib/re/__init__.py`, CPython 3.15.2: pattern
objects, `match`, `fullmatch`, `search`, `findall`, `finditer`, `split`, `sub`, match objects,
`escape`, `Scanner` and the code validator. A callable `repl` or `Scanner` action runs arbitrary
Python, so `sub` takes a literal or template `repl` and `Scanner` takes opaque actions.
-/

namespace PyLean.TextLibs.Re

open PyLean

/-! ### The code validator, `Modules/_sre/sre.c:1776-2265` -/

/-- Why `_validate_inner` stops: `FAIL`, a read outside the code array (which C does not check, so
it is undefined behaviour rather than an outcome), or model fuel. -/
inductive VErr where
  | fail | oob | fuel
  deriving Repr, DecidableEq

abbrev V := Except VErr

/-- `*code`, where nothing in C proves that `code` is inside the array. -/
def vRead (c : Array Nat) (i : Int) : V Nat :=
  if i < 0 ∨ i ≥ c.size then .error .oob else .ok (c.getD i.toNat 0)

/-- `GET_OP`, `GET_ARG`. -/
def vGet (c : Array Nat) (code end_ : Int) : V (Nat × Int) := do
  if code ≥ end_ then throw .fail
  return (← vRead c code, code + 1)

/-- `(uintptr_t)(end - code)`. -/
def uptr (x : Int) : Int := if x < 0 then x + 2 ^ 64 else x

/-- `SRE_CODE` arithmetic. -/
def word32 (x : Int) : Nat := (x % 2 ^ 32).toNat

/-- `GET_SKIP_ADJ(adj)`. -/
def vSkip (c : Array Nat) (code end_ : Int) (adj : Nat) : V (Nat × Int) := do
  if code ≥ end_ then throw .fail
  let skip ← vRead c code
  if (word32 ((skip : Int) - adj) : Int) > uptr (end_ - code) then throw .fail
  return (skip, code + 1)

/-- The byte table check of `SRE_OP_BIGCHARSET`, `Modules/_sre/sre.c:1881-1884`. -/
def vBlocks (c : Array Nat) (code : Int) (arg : Nat) : (n i : Nat) → V Unit
  | 0, _ => .ok ()
  | n + 1, i => do
    let w ← vRead c (code + (i / 4 : Nat))
    if (w / 256 ^ (i % 4)) % 256 ≥ arg then throw .fail
    vBlocks c code arg n (i + 1)

/-- `_validate_charset`, `Modules/_sre/sre.c:1842-1926`. -/
def vCharset (c : Array Nat) : (fuel : Nat) → (code end_ : Int) → V Unit
  | 0, _, _ => .error .fuel
  | fuel + 1, code, end_ => do
    if code ≥ end_ then return ()
    let (op, code) ← vGet c code end_
    if op == OP_NEGATE then vCharset c fuel code end_
    else if op == OP_LITERAL then
      let (_, code) ← vGet c code end_
      vCharset c fuel code end_
    else if op == OP_RANGE || op == OP_RANGE_UNI_IGNORE then
      let (_, code) ← vGet c code end_
      let (_, code) ← vGet c code end_
      vCharset c fuel code end_
    else if op == OP_CHARSET then
      if (8 : Int) > uptr (end_ - code) then throw .fail
      vCharset c fuel (code + 8) end_
    else if op == OP_BIGCHARSET then
      let (arg, code) ← vGet c code end_
      if (64 : Int) > uptr (end_ - code) then throw .fail
      vBlocks c code arg 256 0
      let code := code + 64
      let offset : Int := word32 ((arg : Int) * 8)
      if offset > uptr (end_ - code) then throw .fail
      vCharset c fuel (code + offset) end_
    else if op == OP_CATEGORY then
      let (arg, code) ← vGet c code end_
      if arg ≤ 17 then vCharset c fuel code end_ else throw .fail
    else throw .fail

/-- The overlap table check, `Modules/_sre/sre.c:2052-2055`. -/
def vOverlap (c : Array Nat) (code : Int) (plen : Nat) : (n i : Nat) → V Unit
  | 0, _ => .ok ()
  | n + 1, i => do
    if (← vRead c (code + i)) ≥ plen then throw .fail
    vOverlap c code plen n (i + 1)

/-- The `SRE_OP_INFO` case, `Modules/_sre/sre.c:2013-2071`: the `code` after it. -/
def vInfo (c : Array Nat) (fuel : Nat) (code end_ : Int) : V Int := do
  let (skip, code) ← vSkip c code end_ 0
  let newcode := code + skip - 1
  let (flags, code) ← vGet c code end_
  let (_, code) ← vGet c code end_
  let (_, code) ← vGet c code end_
  if flags &&& (2 ^ 32 - 1 - 7) ≠ 0 then throw .fail
  if flags &&& 1 ≠ 0 ∧ flags &&& 4 ≠ 0 then throw .fail
  if flags &&& 2 ≠ 0 ∧ flags &&& 1 = 0 then throw .fail
  let code ←
    if flags &&& 1 ≠ 0 then do
      let (plen, code) ← vGet c code end_
      let (_, code) ← vGet c code end_
      if (plen : Int) > uptr (newcode - code) then throw .fail
      let code := code + plen
      if (plen : Int) > uptr (newcode - code) then throw .fail
      vOverlap c code plen plen 0
      pure (code + plen)
    else pure code
  if flags &&& 4 ≠ 0 then
    vCharset c fuel code (newcode - 1)
    if (← vRead c (newcode - 1)) != OP_FAILURE then throw .fail
    return newcode
  else if code != newcode then throw .fail
  else return code

mutual
  /-- `_validate_inner`, `Modules/_sre/sre.c:1929-2243`: `0`, or `1` when the last op is `JUMP`. -/
  def vInner (c : Array Nat) (groups : Nat) : (fuel : Nat) → (code end_ : Int) → V Nat
    | 0, _, _ => .error .fuel
    | fuel + 1, code, end_ =>
      if code > end_ then .error .fail else vLoop c groups fuel code end_

  /-- The `while (code < end)`. -/
  def vLoop (c : Array Nat) (groups : Nat) : (fuel : Nat) → (code end_ : Int) → V Nat
    | 0, _, _ => .error .fuel
    | fuel + 1, code, end_ => do
      if code ≥ end_ then return 0
      let (op, code) ← vGet c code end_
      if op == OP_MARK then
        let (arg, code) ← vGet c code end_
        if arg ≥ 2 * groups then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_LITERAL || op == OP_NOT_LITERAL || op == OP_LITERAL_IGNORE ||
          op == OP_NOT_LITERAL_IGNORE || op == OP_LITERAL_UNI_IGNORE ||
          op == OP_NOT_LITERAL_UNI_IGNORE || op == OP_LITERAL_LOC_IGNORE ||
          op == OP_NOT_LITERAL_LOC_IGNORE then
        let (_, code) ← vGet c code end_
        vLoop c groups fuel code end_
      else if op == OP_SUCCESS || op == OP_FAILURE || op == OP_ANY || op == OP_ANY_ALL then
        vLoop c groups fuel code end_
      else if op == OP_AT then
        let (arg, code) ← vGet c code end_
        if arg ≤ 11 then vLoop c groups fuel code end_ else throw .fail
      else if op == OP_IN || op == OP_IN_IGNORE || op == OP_IN_UNI_IGNORE ||
          op == OP_IN_LOC_IGNORE then
        let (skip, code) ← vSkip c code end_ 0
        vCharset c fuel code (code + skip - 2)
        if (← vRead c (code + word32 ((skip : Int) - 2))) != OP_FAILURE then throw .fail
        vLoop c groups fuel (code + word32 ((skip : Int) - 1)) end_
      else if op == OP_INFO then
        vLoop c groups fuel (← vInfo c fuel code end_) end_
      else if op == OP_BRANCH then
        vLoop c groups fuel (← vBranch c groups fuel code end_ none) end_
      else if op == OP_REPEAT_ONE || op == OP_MIN_REPEAT_ONE || op == OP_POSSESSIVE_REPEAT_ONE then
        let (skip, code) ← vSkip c code end_ 0
        let (mn, code) ← vGet c code end_
        let (mx, code) ← vGet c code end_
        if mn > mx then throw .fail
        if mx > 2 ^ 32 - 1 then throw .fail
        if (← vInner c groups fuel code (code + skip - 4)) != 0 then throw .fail
        let code := code + word32 ((skip : Int) - 4)
        let (op2, code) ← vGet c code end_
        if op2 != OP_SUCCESS then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_REPEAT || op == OP_POSSESSIVE_REPEAT then
        let (skip, code) ← vSkip c code end_ 0
        let (mn, code) ← vGet c code end_
        let (mx, code) ← vGet c code end_
        if mn > mx then throw .fail
        if mx > 2 ^ 32 - 1 then throw .fail
        if (← vInner c groups fuel code (code + skip - 3)) != 0 then throw .fail
        let code := code + word32 ((skip : Int) - 3)
        let (op2, code) ← vGet c code end_
        if op == OP_POSSESSIVE_REPEAT then
          if op2 != OP_SUCCESS then throw .fail
        else if op2 != OP_MAX_UNTIL && op2 != OP_MIN_UNTIL then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_ATOMIC_GROUP then
        let (skip, code) ← vSkip c code end_ 0
        if (← vInner c groups fuel code (code + skip - 2)) != 0 then throw .fail
        let code := code + word32 ((skip : Int) - 2)
        let (op2, code) ← vGet c code end_
        if op2 != OP_SUCCESS then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_GROUPREF || op == OP_GROUPREF_IGNORE || op == OP_GROUPREF_UNI_IGNORE ||
          op == OP_GROUPREF_LOC_IGNORE then
        let (arg, code) ← vGet c code end_
        if arg ≥ groups then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_GROUPREF_EXISTS then
        let (arg, code) ← vGet c code end_
        if arg ≥ groups then throw .fail
        let (skip, code) ← vSkip c code end_ 1
        let code := code - 1
        let rc ← vInner c groups fuel (code + 1) (code + skip - 1)
        if rc == 1 then
          let code := code + word32 ((skip : Int) - 2)
          let (skip, code) ← vSkip c code end_ 0
          if (← vInner c groups fuel code (code + skip - 1)) != 0 then throw .fail
          vLoop c groups fuel (code + word32 ((skip : Int) - 1)) end_
        else if rc != 0 then throw .fail
        else vLoop c groups fuel (code + word32 ((skip : Int) - 1)) end_
      else if op == OP_ASSERT || op == OP_ASSERT_NOT then
        let (skip, code) ← vSkip c code end_ 0
        let (_, code) ← vGet c code end_
        let code := code - 1
        if (← vInner c groups fuel (code + 1) (code + skip - 2)) != 0 then throw .fail
        let code := code + word32 ((skip : Int) - 2)
        let (op2, code) ← vGet c code end_
        if op2 != OP_SUCCESS then throw .fail
        vLoop c groups fuel code end_
      else if op == OP_JUMP then
        if code + 1 != end_ then throw .fail
        return 1
      else throw .fail

  /-- The `for (;;)` of `SRE_OP_BRANCH`, `Modules/_sre/sre.c:2076-2096`. -/
  def vBranch (c : Array Nat) (groups : Nat) : (fuel : Nat) → (code end_ : Int) → Option Int → V Int
    | 0, _, _, _ => .error .fuel
    | fuel + 1, code, end_, target => do
      let (skip, code) ← vSkip c code end_ 0
      if skip == 0 then
        if some code != target then throw .fail
        return code
      if (← vInner c groups fuel code (code + skip - 3)) != 0 then throw .fail
      let code := code + word32 ((skip : Int) - 3)
      let (op, code) ← vGet c code end_
      if op != OP_JUMP then throw .fail
      let (skip, code) ← vSkip c code end_ 0
      match target with
      | none => vBranch c groups fuel code end_ (some (code + skip - 1))
      | some t =>
        if code + skip - 1 != t then throw .fail
        vBranch c groups fuel code end_ target
end

/-- `SRE_MAXGROUPS`, `Modules/_sre/sre.h:21`. -/
def SRE_MAXGROUPS : Nat := (2 ^ 31 - 1) / 2

/-- `_validate_outer`, `Modules/_sre/sre.c:2245-2252`. -/
def vOuter (c : Array Nat) (groups : Int) : V Nat :=
  let end_ : Int := c.size
  if groups < 0 ∨ groups > SRE_MAXGROUPS ∨ 0 ≥ end_ then .error .fail
  else
    match vRead c (end_ - 1) with
    | .error e => .error e
    | .ok w =>
      if w != OP_SUCCESS then .error .fail
      else vInner c groups.toNat (3 * c.size + 8) 0 (end_ - 1)

/-- `_validate`, `Modules/_sre/sre.c:2254-2265`. `vOuter` returning `1` is `true` in C. -/
def validate (c : Array Nat) (groups : Int) : Py Unit :=
  match vOuter c groups with
  | .ok 0 => .ok ()
  | .ok _ | .error .fail => .error (.named "RuntimeError" "invalid SRE code")
  | .error .oob => .error (.named "SegmentationFault" "")
  | .error .fuel => .error .modelFuel

/-- The copy into `self->code`, `Modules/_sre/sre.c:1654-1666`, then `_validate`. -/
def sreCompileCheck (c : Array Nat) (groups : Int) : Py Unit :=
  if c.any (· ≥ 2 ^ 32) then
    .error (.overflowError "regular expression code size limit exceeded")
  else validate c groups

/-- A compiled pattern: `PatternObject`. `isbytes` is `0`, `1` or, for `pattern=None`, `-1`. -/
structure Pat where
  pattern : Option (List Nat)
  code : Array Nat
  groups : Nat
  groupindex : List (List Nat × Nat)
  /-- `indexgroup[i]`: what `lastgroup` reads. -/
  isbytes : Int
  flags : Nat
  deriving Repr, Inhabited

/-- `Pat.istext`: how `parse_template` treats a pattern. -/
def Pat.istext (p : Pat) : Bool := p.isbytes ≤ 0

/-- `_compiler.compile`, `Lib/re/_compiler.py:757-782`, without the `dis` of `DEBUG`, followed by
`_sre_compile_impl`, `Modules/_sre/sre.c:1626-1710`. -/
def compilePat (istext : Bool) (s : List Nat) (flags : Nat) (maxDigits : Nat := 4300) : Py Pat := do
  let p ← parse istext s flags maxDigits
  let c ← codeOf p flags
  let code := c.toArray
  validate code (p.groups - 1 : Nat)
  return ⟨some s, code, p.groups - 1, p.groupdict, if istext then 0 else 1, flags ||| p.flags⟩

/-- A `Match`: `mark[2*i]`, `mark[2*i+1]` as a span per group, group 0 first. -/
structure MatchR where
  spans : List (Option (Nat × Nat))
  lastindex : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- `pattern_new_match`, `Modules/_sre/sre.c:2726-2798`, on success. -/
def newMatch (p : Pat) (st : SSt) : Py MatchR := do
  let groupSpans := (List.range p.groups).map fun i =>
    let j : Nat := 2 * i
    if (j : Int) + 1 ≤ st.lastmark then
      match st.mark[j]!, st.mark[j + 1]! with
      | some a, some b => some (a, b)
      | _, _ => none
    else none
  if groupSpans.any (fun s => match s with
      | some (a, b) => a > b
      | none => false) then
    throw (.named "SystemError"
      "The span of capturing group is wrong, please report a bug for the re module.")
  return ⟨some (st.start, st.ptr) :: groupSpans,
    if st.lastindex < 0 then none else some st.lastindex.toNat⟩

/-- The boundary adjustment of `state_init`, `Modules/_sre/sre.c:575-584`. -/
def clampPos (n : Int) (len : Nat) : Nat :=
  if n < 0 then 0 else if n > (len : Int) then len else n.toNat

def initState (p : Pat) (start : Nat) : SSt :=
  { ptr := start, start, mark := Array.replicate (2 * p.groups) none }

def envOf (p : Pat) (s : List Nat) (endp : Nat) (matchAll : Bool) : Env :=
  ⟨p.code, s.toArray, endp, matchAll, true⟩

/-- The type checks of `state_init`, `Modules/_sre/sre.c:562-571`. -/
def checkSubject (p : Pat) (isbytes : Bool) : Py Unit :=
  if isbytes ∧ p.isbytes = 0 then
    .error (.typeError "cannot use a string pattern on a bytes-like object")
  else if !isbytes ∧ p.isbytes > 0 then
    .error (.typeError "cannot use a bytes pattern on a string-like object")
  else .ok ()

/-- `_sre_SRE_Pattern_match_impl`, `fullmatch` and `search`, `Modules/_sre/sre.c:781-903`. -/
def runMatch (p : Pat) (s : List Nat) (pos endpos : Int) (mode : String) : Py (Option MatchR) := do
  let start := clampPos pos s.length
  let endp := clampPos endpos s.length
  let e := envOf p s endp (mode == "fullmatch")
  let st := initState p start
  let r := if mode == "search" then sreSearch e st else matchAt e e.mfuel 0 true st
  match r with
  | none => throw .modelFuel
  | some (false, _) => return none
  | some (true, st) => return some (← newMatch p st)

/-- A group's text, or `None`. -/
inductive GroupV where
  | str (s : List Nat)
  | none
  deriving Repr, DecidableEq, Inhabited

def slice (s : List Nat) (i j : Nat) : List Nat := (s.drop i).take (j - i)

/-- `state_getslice`, `Modules/_sre/sre.c:653-681`. -/
def stateGetslice (st : SSt) (s : List Nat) (index : Nat) (empty : Bool) : Py GroupV :=
  let i : Nat := (index - 1) * 2
  let missing :=
    if (i : Int) ≥ st.lastmark then true
    else (st.mark[i]!).isNone || (st.mark[i + 1]!).isNone
  if missing then .ok (if empty then .str [] else .none)
  else
    let a := (st.mark[i]!).getD 0
    let b := (st.mark[i + 1]!).getD 0
    if a > b then
      .error (.named "SystemError"
        "The span of capturing group is wrong, please report a bug for the re module.")
    else .ok (.str (slice s a b))

/-- What `findall` appends. -/
inductive FindItem where
  | one (v : GroupV)
  | tuple (vs : List GroupV)
  deriving Repr, DecidableEq, Inhabited

/-- `state_reset`, `Modules/_sre/sre.c:487-499`. -/
def stateReset (st : SSt) : SSt :=
  { st with lastmark := -1, lastindex := -1, repeat_ := none, reps := #[] }

/-- The `switch (self->groups)` of `findall`, `Modules/_sre/sre.c:955-980`. -/
def findItem (p : Pat) (s : List Nat) (st : SSt) : Py FindItem :=
  if p.groups == 0 then pure (FindItem.one (.str (slice s st.start st.ptr)))
  else if p.groups == 1 then do
    pure (FindItem.one (← stateGetslice st s 1 true))
  else do
    let vs ← (List.range p.groups).mapM (fun i => stateGetslice st s (i + 1) true)
    pure (FindItem.tuple vs)

/-- The loop of `findall`, `Modules/_sre/sre.c:934-990`. -/
def findallLoop (p : Pat) (e : Env) (s : List Nat) : (fuel : Nat) → SSt → Py (List FindItem)
  | 0, _ => .error .modelFuel
  | fuel + 1, st =>
    if st.start > e.endp then .ok []
    else
      let st := stateReset { st with ptr := st.start }
      match sreSearch e st with
      | none => .error .modelFuel
      | some (false, _) => .ok []
      | some (true, st) => do
        let item ← findItem p s st
        let rest ← findallLoop p e s fuel
          { st with mustAdvance := st.ptr == st.start, start := st.ptr }
        return item :: rest

/-- `_sre_SRE_Pattern_findall_impl`, `Modules/_sre/sre.c:915-1000`. -/
def findall (p : Pat) (s : List Nat) (pos endpos : Int) : Py (List FindItem) :=
  let e := envOf p s (clampPos endpos s.length) false
  findallLoop p e s (2 * s.length + 4) (initState p (clampPos pos s.length))

/-- Repeated `_sre_SRE_Scanner_search_impl` or `match_impl`, `Modules/_sre/sre.c:2865-2954`. -/
def scanLoop (p : Pat) (e : Env) (search : Bool) : (fuel : Nat) → SSt → Py (List MatchR)
  | 0, _ => .error .modelFuel
  | fuel + 1, st =>
    let st := stateReset { st with ptr := st.start }
    match (if search then sreSearch e st else matchAt e e.mfuel 0 true st) with
    | none => .error .modelFuel
    | some (false, _) => .ok []
    | some (true, st) => do
      let m ← newMatch p st
      let rest ← scanLoop p e search fuel
        { st with mustAdvance := st.ptr == st.start, start := st.ptr }
      return m :: rest

/-- `finditer` (`search`) or a `scanner().match` loop, to the first `None`. -/
def scanAll (p : Pat) (s : List Nat) (pos endpos : Int) (search : Bool) : Py (List MatchR) :=
  let e := envOf p s (clampPos endpos s.length) false
  scanLoop p e search (2 * s.length + 4) (initState p (clampPos pos s.length))

/-- The loop of `split`, `Modules/_sre/sre.c:1101-1145`. -/
def splitLoop (p : Pat) (e : Env) (s : List Nat) (maxsplit : Int) :
    (fuel : Nat) → Nat → Int → SSt → Py (List GroupV × Nat)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, last, n, st =>
    if maxsplit ≠ 0 ∧ n ≥ maxsplit then .ok ([], last)
    else
      let st := stateReset { st with ptr := st.start }
      match sreSearch e st with
      | none => .error .modelFuel
      | some (false, _) => .ok ([], last)
      | some (true, st) => do
        let seg := GroupV.str (slice s last st.start)
        let gs ← (List.range p.groups).mapM (fun i => stateGetslice st s (i + 1) false)
        let (rest, l) ← splitLoop p e s maxsplit fuel st.ptr (n + 1)
          { st with mustAdvance := st.ptr == st.start, start := st.ptr }
        return (seg :: gs ++ rest, l)

/-- `_sre_SRE_Pattern_split_impl`, `Modules/_sre/sre.c:1074-1166`. -/
def split (p : Pat) (s : List Nat) (maxsplit : Int) : Py (List GroupV) := do
  let e := envOf p s s.length false
  let (items, last) ← splitLoop p e s maxsplit (2 * s.length + 4) 0 0 (initState p 0)
  return items ++ [.str (slice s last s.length)]

/-- `match_getslice_by_index`, `Modules/_sre/sre.c:2302-2331`. -/
def matchSlice (s : List Nat) (m : MatchR) (i : Nat) : GroupV :=
  match m.spans.getD i none with
  | some (a, b) => .str (slice s a b)
  | none => .none

/-- `_sre_SRE_Match_groups_impl`, `Modules/_sre/sre.c:2456-2477`, with `default=None`. -/
def matchGroups (s : List Nat) (m : MatchR) : List GroupV :=
  (List.range (m.spans.length - 1)).map fun i => matchSlice s m (i + 1)

/-- `_sre_SRE_Match_groupdict_impl`, `Modules/_sre/sre.c:2490-2528`. -/
def matchGroupdict (p : Pat) (s : List Nat) (m : MatchR) : List (List Nat × GroupV) :=
  p.groupindex.map fun x => (x.1, matchSlice s m x.2)

/-- `match_lastgroup_get`, `Modules/_sre/sre.c:2684-2697`. -/
def matchLastgroup (p : Pat) (m : MatchR) : Option (List Nat) :=
  match m.lastindex with
  | none => none
  | some i => (p.groupindex.find? (·.2 == i)).map (·.1)

/-- `expand_template`, `Modules/_sre/sre.c:3022-3085`, on `parse_template`'s items. -/
def expandTemplate (items : List TItem) (s : List Nat) (m : MatchR) : Py (List Nat) :=
  items.foldlM (init := []) fun acc it =>
    match it with
    | .lit l => .ok (acc ++ l)
    | .group g =>
      if g ≥ m.spans.length then .error (.indexError "no such group")
      else match matchSlice s m g with
        | .str t => .ok (acc ++ t)
        | .none => .ok acc

/-- `_sre_SRE_Match_expand_impl`, `Modules/_sre/sre.c:2390-2399`. -/
def matchExpand (p : Pat) (repl s : List Nat) (m : MatchR) : Py (List Nat) := do
  expandTemplate (← parseTemplate p.istext repl p.groups p.groupindex) s m

/-- The replacement of `pattern_subx`: a literal, or a template. -/
inductive Filter where
  | literal (l : List Nat)
  | template (items : List TItem)
  deriving Repr, DecidableEq, Inhabited

/-- The `if (filter_type != LITERAL)` of `pattern_subx`, `Modules/_sre/sre.c:1326-1356`. -/
def subItem (p : Pat) (s : List Nat) (f : Filter) (st : SSt) : Py (List Nat) :=
  match f with
  | .literal l => pure l
  | .template t => do expandTemplate t s (← newMatch p st)

/-- The loop of `pattern_subx`, `Modules/_sre/sre.c:1304-1370`: output, `i` and `n`. -/
def subLoop (p : Pat) (e : Env) (s : List Nat) (f : Filter) (count : Int) :
    (fuel : Nat) → (i : Nat) → (n : Int) → SSt → Py (List Nat × Nat × Int)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, i, n, st =>
    if count ≠ 0 ∧ n ≥ count then .ok ([], i, n)
    else
      let st := stateReset { st with ptr := st.start }
      match sreSearch e st with
      | none => .error .modelFuel
      | some (false, _) => .ok ([], i, n)
      | some (true, st) => do
        let b := st.start
        let en := st.ptr
        let pre := if i < b then slice s i b else []
        let item ← subItem p s f st
        let (rest, i2, n2) ← subLoop p e s f count fuel en (n + 1)
          { st with mustAdvance := st.ptr == st.start, start := st.ptr }
        return (pre ++ item ++ rest, i2, n2)

/-- `pattern_subx`, `Modules/_sre/sre.c:1227-1420`, for a `str` or `bytes` `repl`. -/
def subx (p : Pat) (repl s : List Nat) (count : Int) (isbytes : Bool := !p.istext) :
    Py (List Nat × Int) := do
  let f ←
    if !repl.contains 92 then pure (Filter.literal repl)
    else do
      let t ← parseTemplate p.istext repl p.groups p.groupindex
      pure (match t with
        | [.lit l] => Filter.literal l
        | _ => Filter.template t)
  checkSubject p isbytes
  let e := envOf p s s.length false
  let (out, i, n) ← subLoop p e s f count (2 * s.length + 4) 0 0 (initState p 0)
  return (out ++ (if i < s.length then slice s i s.length else []), n)

/-- What a callable `repl` returns: an object of the subject's kind, `None`, or another object. The
call itself can raise, and it can call back into `re`, which shares no state with this loop. -/
inductive CallRet where
  | text (l : List Nat)
  | none_
  | other (cls : String)
  deriving Repr, DecidableEq, Inhabited

/-- The loop of `pattern_subx` for a callable, `Modules/_sre/sre.c:1304-1370`. `f k m` is the `k`th
call. The result is the list that is joined at the end, so a wrong type surfaces only after every
call has run. -/
def subCallLoop (p : Pat) (e : Env) (s : List Nat) (f : Nat → MatchR → Py CallRet) (count : Int) :
    (fuel : Nat) → (i : Nat) → (n : Int) → (k : Nat) → SSt → Py (List CallRet × Nat × Int)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, i, n, k, st =>
    if count ≠ 0 ∧ n ≥ count then .ok ([], i, n)
    else
      let st := stateReset { st with ptr := st.start }
      match sreSearch e st with
      | none => .error .modelFuel
      | some (false, _) => .ok ([], i, n)
      | some (true, st) => do
        let b := st.start
        let en := st.ptr
        let pre : List CallRet := if i < b then [.text (slice s i b)] else []
        let m ← newMatch p st
        let r ← f k m
        let item : List CallRet := match r with
          | .none_ => []
          | x => [x]
        let (rest, i2, n2) ← subCallLoop p e s f count fuel en (n + 1) (k + 1)
          { st with mustAdvance := st.ptr == st.start, start := st.ptr }
        return (pre ++ item ++ rest, i2, n2)

/-- `PyUnicode_Join` and `PyBytes_Join` on the list. -/
def joinItems (isbytes : Bool) : List CallRet → Nat → Py (List Nat)
  | [], _ => .ok []
  | .text l :: r, k => do return l ++ (← joinItems isbytes r (k + 1))
  | .none_ :: r, k => joinItems isbytes r (k + 1)
  | .other cls :: _, k =>
    .error (.typeError (if isbytes then s!"sequence item {k}: expected a bytes-like object, {cls} found"
      else s!"sequence item {k}: expected str instance, {cls} found"))

/-- `pattern_subx`, `Modules/_sre/sre.c:1227-1420`, for a callable `repl`. -/
def subCall (p : Pat) (f : Nat → MatchR → Py CallRet) (s : List Nat) (count : Int) (isbytes : Bool) :
    Py (List Nat × Int) := do
  checkSubject p isbytes
  let e := envOf p s s.length false
  let (items, i, n) ← subCallLoop p e s f count (2 * s.length + 4) 0 0 0 (initState p 0)
  let out ← joinItems isbytes
    (items ++ (if i < s.length then [.text (slice s i s.length)] else [])) 0
  return (out, n)

/-! ### Match objects -/

/-- What `match_getindex` is given. `unhashable` is an object `dict` rejects with `TypeError`. -/
inductive GIdx where
  | int (i : Int)
  | name (s : List Nat)
  | unhashable
  deriving Repr, DecidableEq, Inhabited

/-- `match_getindex`, `Modules/_sre/sre.c:2333-2366`. -/
def matchGetindex (p : Pat) (m : MatchR) (g : GIdx) : Py Nat :=
  let check (i : Int) : Py Nat :=
    if i < 0 ∨ i ≥ m.spans.length then .error (.indexError "no such group") else .ok i.toNat
  match g with
  | .int i => check i
  | .name n =>
    if p.groupindex.isEmpty then check (-1)
    else match p.groupindex.lookup n with
      | some i => check i
      | none => check (-1)
  | .unhashable =>
    if p.groupindex.isEmpty then check (-1)
    else .error (.typeError "~unhashable type")

/-- `match_getslice`, `Modules/_sre/sre.c:2368-2378`. -/
def matchGetslice (p : Pat) (s : List Nat) (m : MatchR) (g : GIdx) : Py GroupV := do
  return matchSlice s m (← matchGetindex p m g)

/-- `match_group`, `Modules/_sre/sre.c:2403-2437`: one value, or a tuple for two or more. -/
def matchGroup (p : Pat) (s : List Nat) (m : MatchR) : List GIdx → Py FindItem
  | [] => do return .one (← matchGetslice p s m (.int 0))
  | [g] => do return .one (← matchGetslice p s m g)
  | gs => do return .tuple (← gs.mapM (matchGetslice p s m))

/-- `self->mark[index*2]`, `self->mark[index*2+1]`: `-1` for an undefined group. -/
def markPair (m : MatchR) (i : Nat) : Int × Int :=
  match m.spans.getD i none with
  | some (a, b) => (a, b)
  | none => (-1, -1)

/-- `_sre_SRE_Match_start_impl`, `Modules/_sre/sre.c:2536-2548`. -/
def matchStart (p : Pat) (m : MatchR) (g : GIdx) : Py Int := do
  return (markPair m (← matchGetindex p m g)).1

/-- `_sre_SRE_Match_end_impl`, `Modules/_sre/sre.c:2559-2571`. -/
def matchEnd (p : Pat) (m : MatchR) (g : GIdx) : Py Int := do
  return (markPair m (← matchGetindex p m g)).2

/-- `_sre_SRE_Match_span_impl`, `Modules/_sre/sre.c:2599-2611`. -/
def matchSpan (p : Pat) (m : MatchR) (g : GIdx) : Py (Int × Int) := do
  return markPair m (← matchGetindex p m g)

/-- `match_regs`, `Modules/_sre/sre.c:2613-2636`. -/
def matchRegs (m : MatchR) : List (Int × Int) :=
  (List.range m.spans.length).map (markPair m)

/-- `PyBytes_Repr`, `Objects/bytesobject.c:1480-1552`. -/
def bytesRepr (b : List Nat) : List Nat :=
  let q : Nat := if b.contains 39 && !b.contains 34 then 34 else 39
  let hex (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n
  let one (c : Nat) : List Nat :=
    if c == q || c == 92 then [92, c]
    else if c == 9 then [92, 116]
    else if c == 10 then [92, 110]
    else if c == 13 then [92, 114]
    else if c < 32 || c ≥ 127 then [92, 120, hex (c / 16), hex (c % 16)]
    else [c]
  98 :: q :: b.flatMap one ++ [q]

/-- `%.nR` of the replacement: `repr`, cut to `n` characters. -/
def reprCut (n : Nat) (isbytes : Bool) (s : List Nat) : List Nat :=
  (if isbytes then bytesRepr s else PyLean.UnicodeObj.unicodeRepr s).take n

def asciiNats (s : String) : List Nat := s.toList.map Char.toNat

def decNats (n : Int) : List Nat := asciiNats (toString n)

/-- `match_repr`, `Modules/_sre/sre.c:2708-2722`. -/
def matchRepr (isbytes : Bool) (s : List Nat) (m : MatchR) : List Nat :=
  let g0 := match matchSlice s m 0 with
    | .str t => t
    | .none => []
  let (a, b) := markPair m 0
  asciiNats "<re.Match object; span=(" ++ decNats a ++ asciiNats ", " ++ decNats b ++
    asciiNats "), match=" ++ reprCut 50 isbytes g0 ++ asciiNats ">"

/-- `flag_names`, `Modules/_sre/sre.c:1525-1534`. -/
def flagNames : List (String × Nat) :=
  [("re.IGNORECASE", 2), ("re.LOCALE", 4), ("re.MULTILINE", 8), ("re.DOTALL", 16),
   ("re.UNICODE", 32), ("re.VERBOSE", 64), ("re.DEBUG", 128), ("re.ASCII", 256)]

def hexOf (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- `pattern_repr`, `Modules/_sre/sre.c:1519-1598`. `pattern=None` has `repr` `None`. -/
def patternRepr (p : Pat) : List Nat :=
  let fl0 :=
    if p.isbytes = 0 ∧ p.flags &&& (4 ||| 32 ||| 256) = 32 then p.flags - 32 else p.flags
  let step (acc : List String × Nat) (x : String × Nat) : List String × Nat :=
    if acc.2 &&& x.2 ≠ 0 then (acc.1 ++ [x.1], acc.2 - x.2) else acc
  let (items, rest) := flagNames.foldl step ([], fl0)
  let items := if rest ≠ 0 then items ++ ["0x" ++ hexOf rest] else items
  let shown := match p.pattern with
    | some s => reprCut 200 (p.isbytes > 0) s
    | none => asciiNats "None"
  if items.isEmpty then asciiNats "re.compile(" ++ shown ++ asciiNats ")"
  else asciiNats "re.compile(" ++ shown ++ asciiNats ", " ++
    asciiNats (String.intercalate "|" items) ++ asciiNats ")"

/-- The `Py_EQ` of `pattern_richcompare`, `Modules/_sre/sre.c:3113-3160`. -/
def patEq (a b : Pat) : Bool :=
  a.flags == b.flags && a.isbytes == b.isbytes && a.code.size == b.code.size &&
    a.code == b.code && a.pattern == b.pattern

/-- What `pattern_hash`, `Modules/_sre/sre.c:3088-3111`, mixes. -/
def patHashInput (a : Pat) : Option (List Nat) × Array Nat × Nat × Int × Nat :=
  (a.pattern, a.code, a.flags, a.isbytes, a.code.size)

/-- `_sre_template_impl`, `Modules/_sre/sre.c:1724-1774`, on `[literal, g, literal, ...]`. `none`
stands for an `int` item in a literal slot or a `str` in an index slot, which the model's list
never holds; the check that remains is a negative index. -/
def templateCheck (lits : List (List Nat)) (idx : List Int) : Py Unit :=
  if lits.length != idx.length + 1 then .error (.typeError "invalid template")
  else if idx.any (· < 0) then .error (.typeError "invalid template")
  else .ok ()

/-! ### `Lib/re/__init__.py` -/

/-- `_special_chars_map`, `Lib/re/__init__.py:305`. -/
def specialChars : List Nat := "()[]{}?*+-|^$\\.&~# \t\n\r\x0b\x0c".toList.map Char.toNat

/-- `escape`, `Lib/re/__init__.py:307-315`. -/
def escape (s : List Nat) : List Nat :=
  s.flatMap fun c => if specialChars.contains c then [92, c] else [c]

/-- The first argument of the `re` functions: a `str`, `bytes`, a compiled pattern or another
object. -/
inductive PatArg where
  | text (s : List Nat)
  | bytes (s : List Nat)
  | compiled (p : Pat)
  | other
  deriving Repr, Inhabited

/-- `_compile`, `Lib/re/__init__.py:332-374`. The caches only return an earlier result. -/
def reCompile (pat : PatArg) (flags : Nat) : Py Pat :=
  match pat with
  | .compiled p =>
    if flags ≠ 0 then .error (.valueError "cannot process flags argument with a compiled pattern")
    else .ok p
  | .other => .error (.typeError "first argument must be string or compiled pattern")
  | .text s => compilePat true s flags
  | .bytes s => compilePat false s flags

/-- The positional `*args` of `sub`, `subn` (`first` `count`, `least` `3`) and `split` (`first`
`maxsplit`, `least` `2`), `Lib/re/__init__.py:192-208`: the first argument and `flags`. `kwFirst`
and `kwFlags` are the keywords, `none` for `_zero_sentinel`. -/
def shuffleArgs (fn first : String) (least : Nat) (args : List Int) (kwFirst kwFlags : Option Int) :
    Py (Int × Int) :=
  match args with
  | [] => .ok (kwFirst.getD 0, kwFlags.getD 0)
  | a :: rest =>
    if kwFirst.isSome then .error (.typeError s!"{fn}() got multiple values for argument '{first}'")
    else
      match rest with
      | [] => .ok (a, kwFlags.getD 0)
      | b :: rest =>
        if kwFlags.isSome then .error (.typeError s!"{fn}() got multiple values for argument 'flags'")
        else if !rest.isEmpty then
          .error (.typeError s!"{fn}() takes from {least} to {least + 2} positional arguments but {least + 2 + rest.length} were given")
        else .ok (a, b)

/-- A `Scanner`, `Lib/re/__init__.py:394-413`: its pattern object. `flags` is not passed through
`fix_flags` for the combined pattern, and each phrase is parsed in a state of its own. -/
def scannerInit (istext : Bool) (phrases : List (List Nat)) (flags : Nat) : Py Pat := do
  let parsed ← phrases.mapM (fun ph => do
    let x ← parse istext ph flags
    if x.groupwidths.length ≠ 1 then throw (.valueError "Cannot use capturing groups in re.Scanner")
    return x)
  let n := phrases.length
  let wrap (gid : Nat) (x : Parsed) : List Node := [.subpattern (some gid) 0 0 x.p]
  let alts := parsed.zipIdx.map fun (x, i) => wrap (i + 1) x
  let frags ← parsed.zipIdx.mapM fun (x, i) => do
    let c ← compList x.groupwidths flags x.p
    return [OP_MARK, i * 2] ++ c ++ [OP_MARK, i * 2 + 1]
  let body := frags.foldr (fun c rest => [c.length + 3] ++ c ++ [OP_JUMP, rest.length + 1] ++ rest) [OP_FAILURE]
  let widths := parsed.map fun x => getwidth x.groupwidths x.p
  let lo := widths.foldl (fun acc w => Nat.min acc w.1) MAXWIDTH
  let hi := widths.foldl (fun acc w => Nat.max acc w.2) 0
  let code := (compileInfoW (Nat.min lo MAXWIDTH, Nat.min hi MAXWIDTH) [.branch alts] flags ++
    (OP_BRANCH :: body) ++ [OP_SUCCESS]).toArray
  validate code n
  return ⟨none, code, n, [], -1, flags⟩

/-- `Scanner.scan`, `Lib/re/__init__.py:414-433`: `actions[i]`, `none` for `None`. -/
def scanLoopS {α : Type} [Inhabited α] (actions : List (Option α)) (ms : List MatchR) (i : Nat) :
    List α × Nat :=
  match ms with
  | [] => ([], i)
  | m :: ms =>
    let j := match m.spans.head? with
      | some (some (_, b)) => b
      | _ => 0
    if i == j then ([], i)
    else
      let a := (actions.getD (m.lastindex.getD 1 - 1) none)
      let (r, k) := scanLoopS actions ms j
      (match a with
       | some x => x :: r
       | none => r, k)

def scan {α : Type} [Inhabited α] (p : Pat) (actions : List (Option α)) (s : List Nat) :
    Py (List α × List Nat) := do
  let ms ← scanAll p s 0 s.length false
  let (r, i) := scanLoopS actions ms 0
  return (r, s.drop i)

end PyLean.TextLibs.Re
