import PyLean.TextLibs.ReSem

/-!
The engine against the declarative semantics, and against itself.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- The match of a `str` pattern at position 0, as the spans and `lastindex`. A pattern that does
not compile gives `none`, like a failed match, so that two forms compare only on what they do. -/
def matchSpans (pat s : List Nat) (full : Bool) (flags : Nat := 0) : Option MatchR :=
  match compilePat true pat flags with
  | .error _ => none
  | .ok c =>
    match runMatch c s 0 s.length (if full then "fullmatch" else "match") with
    | .ok m => m
    | .error _ => none

/-- `(?:x)q+`. -/
def possessiveText (x q : List Nat) : List Nat :=
  [40, 63, 58] ++ x ++ [41] ++ q ++ [43]

/-- `(?>(?:x)q)`. -/
def atomicText (x q : List Nat) : List Nat :=
  [40, 63, 62, 40, 63, 58] ++ x ++ [41] ++ q ++ [41]

/-- The docs: "`x{m,n}+` is equivalent to `(?>x{m,n})`". For every `x` and every quantifier. -/
def PossessiveIsAtomic : Prop :=
  ∀ (x q s : List Nat) (full : Bool),
    (matchSpans (possessiveText x q) s full).isSome = (matchSpans (atomicText x q) s full).isSome

theorem possessiveIsAtomic_refuted : ¬PossessiveIsAtomic := by
  intro h
  have := h [97, 43] [123, 50, 125] [97, 97] false
  revert this
  decide +kernel

/-- The same sentence for `x*+`, `x++` and `x?+`, which the docs also state, and which no random
test has separated. The engine's possessive loop and the atomic group over a greedy repeat are
different code, so this needs the simulation of `SemAgreesNoSelfTest`. -/
def PossessiveStarIsAtomic : Prop :=
  ∀ (x s : List Nat) (full : Bool) (q : List Nat),
    q = [42] ∨ q = [43] ∨ q = [63] →
    matchSpans (possessiveText x q) s full = matchSpans (atomicText x q) s full

/-- `re` matches as the declarative semantics says, with possessive repeats as documented. -/
def SemAgreesDocumented : Prop :=
  ∀ (pat s : List Nat) (flags : Nat) (full : Bool), semAgrees false pat flags s full = true

theorem semAgreesDocumented_refuted : ¬SemAgreesDocumented := by
  intro h
  have := h [40, 63, 58, 97, 43, 41, 123, 50, 125, 43] [97, 97] 0 false
  revert this
  decide +kernel

/-- The same with possessive repeats as `re` runs them. A failed path still leaves an end mark
when no repeat is active, which only a conditional inside the group it tests can see. -/
def SemAgreesPerIteration : Prop :=
  ∀ (pat s : List Nat) (flags : Nat) (full : Bool), semAgrees true pat flags s full = true

theorem semAgreesPerIteration_refuted : ¬SemAgreesPerIteration := by
  intro h
  have := h [40, 40, 41, 40, 63, 58, 40, 63, 40, 49, 41, 98, 41, 41, 63, 63, 41] [98] 0 true
  revert this
  decide +kernel

mutual
  /-- No conditional tests a group that is open where it stands. `opens` is the groups open here. -/
  def condsClosed (opens : List Nat) : Node → Bool
    | .grouprefExists g y n =>
      !opens.contains g && condsClosedL opens y &&
        (match n with
         | some l => condsClosedL opens l
         | none => true)
    | .branch alts => condsClosedA opens alts
    | .subpattern (some g) _ _ p => condsClosedL (g :: opens) p
    | .subpattern none _ _ p => condsClosedL opens p
    | .repeat_ _ _ _ p | .atomic p | .assert_ _ p | .assertNot _ p => condsClosedL opens p
    | _ => true

  def condsClosedL (opens : List Nat) : List Node → Bool
    | [] => true
    | n :: ns => condsClosed opens n && condsClosedL opens ns

  def condsClosedA (opens : List Nat) : List (List Node) → Bool
    | [] => true
    | a :: as => condsClosedL opens a && condsClosedA opens as
end

/-- With both excluded cases out, `re` matches as the semantics says: the same end, spans and
`lastindex`. 150000 of 150000 random cases agree on CPython 3.14.7. -/
def SemAgreesNoSelfTest : Prop :=
  ∀ (pat s : List Nat) (flags : Nat) (full : Bool) (p : Parsed), parse true pat flags = .ok p →
    condsClosedL [] p.p = true → semAgrees true pat flags s full = true

/-- `Pattern.match(s, pos, endpos)`: "If `endpos` is less than `pos`, no match will be found", for
every pattern. -/
def EndposBeforePos : Prop :=
  ∀ (pat s : List Nat) (pos endpos : Nat), pos ≤ s.length → endpos < pos →
    (match compilePat true pat 0 with
     | .ok c =>
       (match runMatch c s pos endpos "match" with
        | .ok (some _) => false
        | _ => true)
     | .error _ => true) = true

theorem endposBeforePos_refuted : ¬EndposBeforePos := by
  intro h
  have := h [] [10] 1 0 (by decide) (by decide)
  revert this
  decide +kernel

theorem search_past (c : Pat) (s : List Nat) (pos endpos : Nat) (b : Bool) (h : endpos < pos) :
    sreSearch (envOf c s endpos b) (initState c pos) = some (false, initState c pos) := by
  unfold sreSearch
  exact if_pos h

/-- `search` honours the same sentence: its own first test is `ptr > end`. -/
def EndposBeforePosSearch : Prop :=
  ∀ (c : Pat) (s : List Nat) (pos endpos : Nat), pos ≤ s.length → endpos < pos →
    runMatch c s pos endpos "search" = .ok none

theorem endposBeforePosSearch_proven : EndposBeforePosSearch := by
  intro c s pos endpos h1 h2
  have e1 : clampPos pos s.length = pos := by
    simp only [clampPos]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  have e2 : clampPos endpos s.length = endpos := by
    simp only [clampPos]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  have e3 : ("search" == "search") = true := by decide
  unfold runMatch
  simp only [e1, e2, e3, if_true, bind, Except.bind, pure, Except.pure]
  rw [search_past _ _ _ _ _ h2]

/-- Under `IGNORECASE`, `(x)\\1` matches `x` and `y` whenever `x` as a literal matches `y`. `x` and `y`
are single characters that need no escape, and the group's text is compared as the literal is. -/
def BackrefMatchesLiteral : Prop :=
  ∀ x y : Nat, 97 ≤ x → x ≤ 122 → (matchSpans [x] [y] true FLAG_IGNORECASE).isSome = true →
    (matchSpans [40, x, 41, 92, 49] [x, y] true FLAG_IGNORECASE).isSome = true

theorem backrefMatchesLiteral_refuted : ¬BackrefMatchesLiteral := by
  intro h
  have := h 115 383 (by decide) (by decide) (by decide +kernel)
  revert this
  decide +kernel

end PyLean.TextLibs.Re
