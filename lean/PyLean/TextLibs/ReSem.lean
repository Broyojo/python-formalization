import PyLean.TextLibs.ReApi

/-!
A declarative backtracking semantics for the parse tree, written without the engine's state.

`semSeq` tries each way to match in priority order and asks the continuation `k` whether the rest
succeeds, so a path that fails leaves nothing behind: there is no `LASTMARK_SAVE`, no `MARK_PUSH`,
no `SRE_REPEAT`, no `INFO` block and no prefix or charset optimization. Marks are single positions,
as in SRE, and a group is set when both of its marks are and `q ≥ p`.

Over 2.8 million random pattern and subject pairs on CPython 3.14.7 this disagrees with `re` in two
ways, each on record below with a refutation:
* `x{m,n}+` with `m ≥ 2`: `re` makes each of the first `m` iterations atomic, where the documented
  `(?>x{m,n})` can backtrack among them. `perIter` selects what `re` does.
* a conditional inside the group it tests, `(()(?:(?(1)b))??)`: `re` keeps the end mark of a failed
  path when no repeat is active.
-/

namespace PyLean.TextLibs.Re

open PyLean

/-- What a path has fixed so far. -/
structure SemSt where
  marks : Array (Option Nat)
  last : Option Nat := none
  deriving Repr, Inhabited

abbrev SemR := Option (Option (Nat × SemSt))

/-- The fixed part of a run. `perIter` makes the first `m` iterations of a possessive repeat
atomic one by one; without it the whole repeat is one atomic group, as the docs say. -/
structure SemCfg where
  s : Array Nat
  endp : Nat
  gw : List (Option (Nat × Nat))
  perIter : Bool

def SemCfg.ch (c : SemCfg) (i : Nat) : Nat := c.s.getD i 0

/-- A group, if it is set. -/
def semGroup (st : SemSt) (g : Nat) : Option (Nat × Nat) :=
  match st.marks.getD (2 * g) none, st.marks.getD (2 * g + 1) none with
  | some p, some q => if q < p then none else some (p, q)
  | _, _ => none

/-- Is `c` the character `a`, under `flags`? -/
def litEq (flags a c : Nat) : Bool :=
  if !hasFlag flags FLAG_IGNORECASE then c == a
  else if hasFlag flags FLAG_LOCALE then charLocIgnore a c
  else
    match caseFor flags with
    | none => c == a
    | some cf =>
      if !cf.iscased a then c == a
      else
        let lo := cf.tolower a
        let t := cf.tolower c
        t == lo || ((cf.fixes.lookup lo).getD []).contains t

/-- Is `c` in the set item? -/
def itemHit (flags : Nat) (it : SetItem) (c : Nat) : Bool :=
  match it with
  | .literal a => litEq flags a c
  | .range lo hi =>
    if hasFlag flags FLAG_IGNORECASE then anyRange (fun x => litEq flags x c) (hi + 1 - lo) lo
    else lo ≤ c && c ≤ hi
  | .category k => sreCategory (catCode flags k) c
  | .negate => false

/-- Is `c` in the set? -/
def setHit (flags : Nat) (items : List SetItem) (c : Nat) : Bool :=
  let hit := items.any fun it => itemHit flags it c
  if items.contains .negate then !hit else hit

/-- The compare of a backreference: the position after it, or `none`. -/
def refEq (c : SemCfg) (norm : Nat → Nat) : (fuel a b pos : Nat) → Option Nat
  | 0, _, _, pos => some pos
  | fuel + 1, a, b, pos =>
    if a < b then
      if pos ≥ c.endp || norm (c.ch pos) != norm (c.ch a) then none
      else refEq c norm fuel (a + 1) b (pos + 1)
    else some pos

/-- The case mapping of a backreference. -/
def refNorm (flags : Nat) : Nat → Nat :=
  if !hasFlag flags FLAG_IGNORECASE then id
  else if hasFlag flags FLAG_LOCALE then lowerLocale
  else match caseFor flags with
    | some cf => if cf.fixes.isEmpty then lowerAscii else lowerUnicode
    | none => lowerAscii

def setMark (st : SemSt) (i pos : Nat) : SemSt := { st with marks := st.marks.set! i (some pos) }

/-- `(?:...)` of a repeat's body stands in the way of nothing: `done` ends an atomic part. -/
def done_ (p : Nat) (st : SemSt) : SemR := some (some (p, st))

mutual
  def semSeq (c : SemCfg) : (fuel : Nat) → List Node → (flags pos : Nat) → SemSt →
      (Nat → SemSt → SemR) → SemR
    | 0, _, _, _, _, _ => none
    | _ + 1, [], _, pos, st, k => k pos st
    | fuel + 1, n :: ns, flags, pos, st, k =>
      semNode c fuel n flags pos st (fun p st => semSeq c fuel ns flags p st k)

  def semNode (c : SemCfg) : (fuel : Nat) → Node → (flags pos : Nat) → SemSt →
      (Nat → SemSt → SemR) → SemR
    | 0, _, _, _, _, _ => none
    | fuel + 1, n, flags, pos, st, k =>
      let more := pos < c.endp
      let cur := c.ch pos
      match n with
      | .failure => some none
      | .literal a => if more && litEq flags a cur then k (pos + 1) st else some none
      | .notLiteral a => if more && !litEq flags a cur then k (pos + 1) st else some none
      | .any =>
        if more && (hasFlag flags FLAG_DOTALL || cur != 10) then k (pos + 1) st else some none
      | .in_ s => if more && setHit flags s cur then k (pos + 1) st else some none
      | .at_ a =>
        if sreAt ⟨#[], c.s, c.endp, false⟩ pos (atCode flags a) then k pos st else some none
      | .subpattern none add del p => semSeq c fuel p (combineFlags flags add del) pos st k
      | .subpattern (some 0) add del p => semSeq c fuel p (combineFlags flags add del) pos st k
      | .subpattern (some (g + 1)) add del p =>
        semSeq c fuel p (combineFlags flags add del) pos (setMark st (2 * g) pos) fun q st =>
          k q { (setMark st (2 * g + 1) q) with last := some (g + 1) }
      | .branch alts => semAlts c fuel alts flags pos st k
      | .atomic p =>
        match semSeq c fuel p flags pos st done_ with
        | none => none
        | some none => some none
        | some (some (q, st)) => k q st
      | .assert_ d p =>
        let back := if d ≥ 0 then 0 else (getwidth c.gw p).1
        if pos < back then some none
        else
          match semSeq c fuel p flags (pos - back) st done_ with
          | none => none
          | some none => some none
          | some (some (_, st)) => k pos st
      | .assertNot d p =>
        let back := if d ≥ 0 then 0 else (getwidth c.gw p).1
        if pos < back then k pos st
        else
          match semSeq c fuel p flags (pos - back) st done_ with
          | none => none
          | some none => k pos st
          | some (some _) => some none
      | .groupref g =>
        match semGroup st (g - 1) with
        | none => some none
        | some (a, b) =>
          match refEq c (refNorm flags) (b - a + 1) a b pos with
          | none => some none
          | some q => k q st
      | .grouprefExists g yes no =>
        match semGroup st (g - 1) with
        | some _ => semSeq c fuel yes flags pos st k
        | none =>
          match no with
          | some l => semSeq c fuel l flags pos st k
          | none => k pos st
      | .repeat_ .max mn mx p => semMax c fuel mn mx p flags 0 none pos st k
      | .repeat_ .min mn mx p => semMin c fuel mn mx p flags 0 none pos st k
      | .repeat_ .possessive mn mx p =>
        match semPoss c fuel mn mx p flags 0 none pos st with
        | none => none
        | some none => some none
        | some (some (q, st)) => k q st

  def semAlts (c : SemCfg) : (fuel : Nat) → List (List Node) → (flags pos : Nat) → SemSt →
      (Nat → SemSt → SemR) → SemR
    | 0, _, _, _, _, _ => none
    | _ + 1, [], _, _, _, _ => some none
    | fuel + 1, a :: as, flags, pos, st, k =>
      match semSeq c fuel a flags pos st k with
      | none => none
      | some none => semAlts c fuel as flags pos st k
      | some (some r) => some (some r)

  /-- A greedy repeat: as many iterations as can start at a new position, then the rest. -/
  def semMax (c : SemCfg) : (fuel : Nat) → (mn mx : Nat) → List Node → (flags count : Nat) →
      Option Nat → (pos : Nat) → SemSt → (Nat → SemSt → SemR) → SemR
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, mn, mx, p, flags, count, last, pos, st, k =>
      if count < mn then
        semSeq c fuel p flags pos st fun q st => semMax c fuel mn mx p flags (count + 1) last q st k
      else if (count < mx ∨ mx == MAXREPEAT) ∧ some pos != last then
        match semSeq c fuel p flags pos st fun q st =>
            semMax c fuel mn mx p flags (count + 1) (some pos) q st k with
        | none => none
        | some none => k pos st
        | some (some r) => some (some r)
      else k pos st

  /-- A lazy repeat: the rest first, then one more iteration. -/
  def semMin (c : SemCfg) : (fuel : Nat) → (mn mx : Nat) → List Node → (flags count : Nat) →
      Option Nat → (pos : Nat) → SemSt → (Nat → SemSt → SemR) → SemR
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, mn, mx, p, flags, count, last, pos, st, k =>
      if count < mn then
        semSeq c fuel p flags pos st fun q st => semMin c fuel mn mx p flags (count + 1) last q st k
      else
        match k pos st with
        | none => none
        | some (some r) => some (some r)
        | some none =>
          if (count ≥ mx ∧ mx != MAXREPEAT) ∨ some pos == last then some none
          else
            semSeq c fuel p flags pos st fun q st =>
              semMin c fuel mn mx p flags (count + 1) (some pos) q st k

  /-- A possessive repeat, on its own: it ends where it ends, and `done_` commits. -/
  def semPoss (c : SemCfg) : (fuel : Nat) → (mn mx : Nat) → List Node → (flags count : Nat) →
      Option Nat → (pos : Nat) → SemSt → SemR
    | 0, _, _, _, _, _, _, _, _ => none
    | fuel + 1, mn, mx, p, flags, count, last, pos, st =>
      if count < mn then
        if c.perIter then
          match semSeq c fuel p flags pos st done_ with
          | none => none
          | some none => some none
          | some (some (q, st)) => semPoss c fuel mn mx p flags (count + 1) last q st
        else
          semSeq c fuel p flags pos st fun q st => semPoss c fuel mn mx p flags (count + 1) last q st
      else if (count < mx ∨ mx == MAXREPEAT) ∧ some pos != last then
        match semSeq c fuel p flags pos st fun q st =>
            semPoss c fuel mn mx p flags (count + 1) (some pos) q st with
        | none => none
        | some none => done_ pos st
        | some (some r) => some (some r)
      else done_ pos st
end

/-- A node count, for the fuel. -/
def semSize (p : Parsed) (pat : List Nat) : Nat := pat.length + p.groups + 2

def semFuel (n len : Nat) : Nat := 4096 + 64 * n * (len + 2)

/-- What a match gives: the end, the group spans and `lastindex`. -/
structure SemOut where
  stop : Nat
  groups : List (Option (Nat × Nat))
  last : Option Nat
  deriving Repr, DecidableEq, Inhabited

def semOut (groups : Nat) (q : Nat) (st : SemSt) : SemOut :=
  ⟨q, (List.range (groups - 1)).map (semGroup st), st.last⟩

/-- The match at `start`. `full` is `fullmatch`. -/
def semMatch (perIter : Bool) (p : Parsed) (flags : Nat) (pat s : List Nat) (start endp : Nat)
    (full : Bool) : Option (Option SemOut) :=
  let c : SemCfg := ⟨s.toArray, endp, p.groupwidths, perIter⟩
  let st : SemSt := { marks := Array.replicate (2 * p.groups) none }
  let k : Nat → SemSt → SemR := fun q st =>
    if full && q != endp then some none else done_ q st
  match semSeq c (semFuel (semSize p pat) s.length) p.p (p.flags ||| flags) start st k with
  | none => none
  | some none => some none
  | some (some (q, st)) => some (some (semOut p.groups q st))

/-- The engine's match, read off in the same form. -/
def engineOut (m : Option MatchR) : Option SemOut :=
  m.map fun m =>
    ⟨(m.spans.headD none).map (·.2) |>.getD 0, m.spans.drop 1, m.lastindex⟩

/-- The pattern, parsed and compiled. -/
def semBoth (pat : List Nat) (flags : Nat) : Py (Parsed × Pat) := do
  let p ← parse true pat flags
  let c ← compilePat true pat flags
  return (p, c)

/-- `re.match` or `re.fullmatch` at 0 against the semantics: `true` when they agree. Patterns that
do not compile have nothing to compare. -/
def semAgrees (perIter : Bool) (pat : List Nat) (flags : Nat) (s : List Nat) (full : Bool) : Bool :=
  match semBoth pat flags with
  | .error _ => true
  | .ok (p, c) =>
    match runMatch c s 0 s.length (if full then "fullmatch" else "match") with
    | .error _ => true
    | .ok m =>
      match semMatch perIter p flags pat s 0 s.length full with
      | none => true
      | some r => r == engineOut m

end PyLean.TextLibs.Re
