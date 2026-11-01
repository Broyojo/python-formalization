import PyLean.TextLibs.ReCharset3

/-!
The interface over the matcher. `findall`, `split`, `sub` and `finditer` are four loops over the same
`SRE(search)`; `Match` has several methods that say the same thing. Each law here sets one against
another, for every pattern, so it depends on the loops and methods and not on what the pattern is.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-! ### What a `Match` holds -/

/-- What `pattern_new_match` copies out of the state, as the state gives it. -/
def spanOf (st : SSt) (i : Nat) : Option (Nat × Nat) :=
  let j : Nat := 2 * i
  if (j : Int) + 1 ≤ st.lastmark then
    match st.mark[j]!, st.mark[j + 1]! with
    | some a, some b => some (a, b)
    | _, _ => none
  else none

theorem newMatch_spans {p : Pat} {st : SSt} {m : MatchR} (h : newMatch p st = .ok m) :
    m.spans = some (st.start, st.ptr) :: (List.range p.groups).map (spanOf st) ∧
    (∀ i, i < p.groups → ∀ a b, spanOf st i = some (a, b) → a ≤ b) := by
  unfold newMatch at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i hany
    cases h
    refine ⟨rfl, fun i hi a b hs => Nat.le_of_not_gt fun hlt => hany ?_⟩
    apply List.any_eq_true.2
    refine ⟨some (a, b), ?_, by simp; omega⟩
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi, hs⟩

/-- `state_getslice` reads what the `Match` keeps. -/
theorem getslice_span {p : Pat} {st : SSt} {m : MatchR} (s : List Nat) (empty : Bool)
    (h : newMatch p st = .ok m) (i : Nat) (hi : i < p.groups) :
    stateGetslice st s (i + 1) empty =
      .ok (match matchSlice s m (i + 1) with
        | .none => if empty then .str [] else .none
        | v => v) := by
  obtain ⟨h1, h2⟩ := newMatch_spans h
  have hg : m.spans.getD (i + 1) none = spanOf st i := by
    rw [h1, List.getD_cons_succ]
    simp [List.getD_eq_getElem?_getD, hi]
  unfold matchSlice
  rw [hg]
  unfold stateGetslice
  simp only [Nat.add_sub_cancel]
  rw [show i * 2 = 2 * i by omega]
  by_cases h3 : ((2 * i : Nat) : Int) ≥ st.lastmark
  · have hs : spanOf st i = none := by
      unfold spanOf
      exact if_neg (by omega)
    rw [hs, if_pos h3]
    rfl
  · have h4 : ((2 * i : Nat) : Int) + 1 ≤ st.lastmark := by omega
    have hs : spanOf st i = match st.mark[2 * i]!, st.mark[2 * i + 1]! with
        | some a, some b => some (a, b)
        | _, _ => none := by
      unfold spanOf
      exact if_pos h4
    rw [hs, if_neg h3]
    cases ha : st.mark[2 * i]! with
    | none => rfl
    | some a =>
      cases hb : st.mark[2 * i + 1]! with
      | none => simp
      | some b =>
        have := h2 i hi a b (by rw [hs, ha, hb])
        simp [Nat.not_lt.2 this]

/-! ### Four loops, one search -/

/-- What `findall` makes of a match. -/
def itemOf (p : Pat) (s : List Nat) (m : MatchR) : FindItem :=
  let v (i : Nat) : GroupV := match matchSlice s m i with
    | .none => .str []
    | x => x
  if p.groups == 0 then .one (matchSlice s m 0)
  else if p.groups == 1 then .one (v 1)
  else .tuple ((List.range p.groups).map fun i => v (i + 1))

theorem mapM_range_ok {α : Type} (f : Nat → Py α) (g : Nat → α) : ∀ n : Nat,
    (∀ i, i < n → f i = .ok (g i)) → (List.range n).mapM f = .ok ((List.range n).map g) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [List.range_succ, List.mapM_append, ih (fun i hi => h i (by omega))]
    simp [h n (by omega), bind, Except.bind, pure, Except.pure]

theorem item_step (p : Pat) (s : List Nat) (st : SSt) (m : MatchR) (h : newMatch p st = .ok m) :
    findItem p s st = .ok (itemOf p s m) := by
  obtain ⟨h1, _⟩ := newMatch_spans h
  have hg : ∀ i, i < p.groups → stateGetslice st s (i + 1) true =
      .ok (match matchSlice s m (i + 1) with
        | .none => .str []
        | x => x) := fun i hi => by
    rw [getslice_span s true h i hi]
    rfl
  unfold itemOf findItem
  by_cases h0 : p.groups == 0
  · simp only [h0, if_true, matchSlice, h1]
    rfl
  · simp only [h0, Bool.false_eq_true, if_false]
    have hne : p.groups ≠ 0 := by simpa using h0
    by_cases h2 : p.groups == 1
    · have hone : p.groups = 1 := by simpa using h2
      simp only [h2, if_true, bind, Except.bind, pure, Except.pure]
      rw [hg 0 (by omega)]
    · simp only [h2, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure]
      rw [mapM_range_ok _ _ _ hg]

/-- `findall` is `finditer`, with each match read the way the docs say: the whole match, the group,
or the tuple of groups, with `''` for a group that did not take part. For every pattern. -/
def FindallIsFinditer : Prop :=
  ∀ (p : Pat) (e : Env) (s : List Nat) (fuel : Nat) (st : SSt) (ms : List MatchR),
    scanLoop p e true fuel st = .ok ms → findallLoop p e s fuel st = .ok (ms.map (itemOf p s))

theorem findallIsFinditer_proven : FindallIsFinditer := by
  intro p e s fuel
  induction fuel with
  | zero =>
    intro st ms h
    simp [scanLoop] at h
  | succ fuel ih =>
    intro st ms h
    simp only [scanLoop, if_true] at h
    by_cases hs : st.start > e.endp
    · have hpast : sreSearch e (stateReset { st with ptr := st.start }) =
          some (false, stateReset { st with ptr := st.start }) := by
        unfold sreSearch
        exact if_pos hs
      rw [hpast] at h
      cases h
      simp [findallLoop, hs]
    · cases hr : sreSearch e (stateReset { st with ptr := st.start }) with
      | none =>
        rw [hr] at h
        cases h
      | some x =>
        obtain ⟨ok, st2⟩ := x
        rw [hr] at h
        cases ok with
        | false =>
          cases h
          simp [findallLoop, hs, hr]
        | true =>
          simp only [bind, Except.bind, pure, Except.pure] at h
          cases hn : newMatch p st2 with
          | error e' =>
            rw [hn] at h
            cases h
          | ok m =>
            rw [hn] at h
            simp only at h
            cases hrest : scanLoop p e true fuel
                { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } with
            | error e' =>
              rw [hrest] at h
              cases h
            | ok ms2 =>
              rw [hrest] at h
              cases h
              rw [findallLoop, if_neg hs]
              dsimp only
              rw [hr]
              dsimp only
              rw [item_step p s st2 m hn]
              simp only [bind, Except.bind, pure, Except.pure]
              rw [ih _ _ hrest]
              rfl

/-- The whole match of a `Match`. -/
def span0 (m : MatchR) : Nat × Nat := (m.spans.getD 0 none).getD (0, 0)

theorem span0_of {p : Pat} {st : SSt} {m : MatchR} (h : newMatch p st = .ok m) :
    span0 m = (st.start, st.ptr) := by
  obtain ⟨h1, _⟩ := newMatch_spans h
  simp [span0, h1]

/-- What `split` makes of the matches `finditer` finds. -/
def splitPieces (p : Pat) (s : List Nat) (last : Nat) : List MatchR → List GroupV × Nat
  | [] => ([], last)
  | m :: ms =>
    let r := splitPieces p s (span0 m).2 ms
    (.str (slice s last (span0 m).1) :: (List.range p.groups).map (fun i => matchSlice s m (i + 1)) ++ r.1, r.2)

/-- The state a loop goes on with after a match. -/
def nextSt (st : SSt) : SSt := { st with mustAdvance := st.ptr == st.start, start := st.ptr }

/-- What a loop over `SRE(search)` can see of `scanLoop`: its step. -/
theorem scan_step {p : Pat} {e : Env} {fuel : Nat} {st : SSt} {ms : List MatchR}
    (h : scanLoop p e true (fuel + 1) st = .ok ms) :
    (∃ x, sreSearch e (stateReset { st with ptr := st.start }) = some (false, x) ∧ ms = []) ∨
    (∃ st2 m ms2, sreSearch e (stateReset { st with ptr := st.start }) = some (true, st2) ∧
      newMatch p st2 = .ok m ∧ scanLoop p e true fuel (nextSt st2) = .ok ms2 ∧ ms = m :: ms2) := by
  simp only [scanLoop, if_true] at h
  cases hr : sreSearch e (stateReset { st with ptr := st.start }) with
  | none =>
    rw [hr] at h
    cases h
  | some x =>
    obtain ⟨ok, st2⟩ := x
    rw [hr] at h
    cases ok with
    | false =>
      cases h
      exact .inl ⟨_, rfl, rfl⟩
    | true =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      cases hn : newMatch p st2 with
      | error e' =>
        rw [hn] at h
        cases h
      | ok m =>
        rw [hn] at h
        simp only at h
        cases hrest : scanLoop p e true fuel (nextSt st2) with
        | error e' =>
          have : scanLoop p e true fuel { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } =
              .error e' := hrest
          rw [this] at h
          cases h
        | ok ms2 =>
          have : scanLoop p e true fuel { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } =
              .ok ms2 := hrest
          rw [this] at h
          cases h
          exact .inr ⟨st2, m, ms2, rfl, hn, hrest, rfl⟩

/-- `split` cuts at the spans `finditer` finds, and keeps the groups. For every pattern, including
those that match the empty string, where the two share `must_advance`. -/
def SplitIsFinditer : Prop :=
  ∀ (p : Pat) (e : Env) (s : List Nat) (fuel last : Nat) (n : Int) (st : SSt) (ms : List MatchR),
    scanLoop p e true fuel st = .ok ms → splitLoop p e s 0 fuel last n st = .ok (splitPieces p s last ms)

theorem splitIsFinditer_proven : SplitIsFinditer := by
  intro p e s fuel
  induction fuel with
  | zero =>
    intro last n st ms h
    simp [scanLoop] at h
  | succ fuel ih =>
    intro last n st ms h
    rcases scan_step h with ⟨x, h1, rfl⟩ | ⟨st2, m, ms2, h1, h2, h3, rfl⟩
    · simp [splitLoop, h1, splitPieces]
    · have hsp := span0_of h2
      have hgs : (List.range p.groups).mapM (fun i => stateGetslice st2 s (i + 1) false) =
          .ok ((List.range p.groups).map fun i => matchSlice s m (i + 1)) := by
        apply mapM_range_ok
        intro i hi
        rw [getslice_span s false h2 i hi]
        cases matchSlice s m (i + 1) <;> rfl
      rw [splitLoop]
      simp only [ne_eq, not_true_eq_false, false_and, if_false, h1, bind, Except.bind, pure,
        Except.pure, hgs]
      have hr := ih st2.ptr (n + 1) (nextSt st2) ms2 h3
      have hn : splitLoop p e s 0 fuel st2.ptr (n + 1)
          { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } =
          .ok (splitPieces p s st2.ptr ms2) := hr
      rw [hn]
      simp only [splitPieces, hsp]

/-- The output of a replacement over the matches, with `items` in place of each. -/
def subPieces (s : List Nat) (i : Nat) (n : Int) : List MatchR → List (List Nat) → List Nat × Nat × Int
  | m :: ms, it :: its =>
    let r := subPieces s (span0 m).2 (n + 1) ms its
    ((if i < (span0 m).1 then slice s i (span0 m).1 else []) ++ it ++ r.1, r.2)
  | _, _ => ([], i, n)

/-- What the filter gives for a match. -/
def filterOf (s : List Nat) (f : Filter) (m : MatchR) : Py (List Nat) :=
  match f with
  | .literal l => .ok l
  | .template t => expandTemplate t s m

/-- `sub` with a string replacement rebuilds the subject from what `finditer` finds, with a literal
or an expanded template at each match. A template that fails fails the whole call. -/
def SubIsFinditer : Prop :=
  ∀ (p : Pat) (e : Env) (s : List Nat) (f : Filter) (fuel i : Nat) (n : Int) (st : SSt)
    (ms : List MatchR),
    scanLoop p e true fuel st = .ok ms →
    subLoop p e s f 0 fuel i n st = (do
      let its ← ms.mapM (filterOf s f)
      return subPieces s i n ms its)

theorem subIsFinditer_proven : SubIsFinditer := by
  intro p e s f fuel
  induction fuel with
  | zero =>
    intro i n st ms h
    simp [scanLoop] at h
  | succ fuel ih =>
    intro i n st ms h
    rcases scan_step h with ⟨x, h1, rfl⟩ | ⟨st2, m, ms2, h1, h2, h3, rfl⟩
    · simp [subLoop, h1, subPieces, bind, Except.bind, pure, Except.pure]
    · have hsp := span0_of h2
      have hitem : subItem p s f st2 = filterOf s f m := by
        cases f with
        | literal l => rfl
        | template t =>
          simp only [subItem, filterOf, bind, Except.bind, h2]
      have hr := ih st2.ptr (n + 1) (nextSt st2) ms2 h3
      have hn : subLoop p e s f 0 fuel st2.ptr (n + 1)
          { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } =
          (do let its ← ms2.mapM (filterOf s f); return subPieces s st2.ptr (n + 1) ms2 its) := hr
      rw [subLoop]
      simp only [ne_eq, not_true_eq_false, false_and, if_false, h1]
      simp only [hitem, hn, List.mapM_cons, bind, Except.bind, pure, Except.pure]
      cases filterOf s f m with
      | error x => rfl
      | ok it =>
        simp only
        cases ms2.mapM (filterOf s f) with
        | error x => rfl
        | ok its => simp only [subPieces, hsp]

/-- The calls a callable `repl` gets, in order, stopping at the first that raises. -/
def callAll (f : Nat → MatchR → Py CallRet) : Nat → List MatchR → Py (List CallRet)
  | _, [] => .ok []
  | k, m :: ms => do
    let r ← f k m
    return r :: (← callAll f (k + 1) ms)

/-- The list `pattern_subx` joins. -/
def subCallPieces (s : List Nat) (i : Nat) (n : Int) : List MatchR → List CallRet → List CallRet × Nat × Int
  | m :: ms, r :: rs =>
    let t := subCallPieces s (span0 m).2 (n + 1) ms rs
    ((if i < (span0 m).1 then [.text (slice s i (span0 m).1)] else []) ++
      (match r with
       | .none_ => []
       | x => [x]) ++ t.1, t.2)
  | _, _ => ([], i, n)

/-- A callable `repl` is called once per match, in order, on the match `finditer` gives. A call that
raises ends `sub` with that exception and no later call runs; a result of the wrong type surfaces
only at the join, after every call. `f` is an arbitrary function of the call number and the match,
so this holds for any callable. -/
def SubCallIsFinditer : Prop :=
  ∀ (p : Pat) (e : Env) (s : List Nat) (f : Nat → MatchR → Py CallRet) (fuel i k : Nat) (n : Int)
    (st : SSt) (ms : List MatchR),
    scanLoop p e true fuel st = .ok ms →
    subCallLoop p e s f 0 fuel i n k st = (do
      let rs ← callAll f k ms
      return subCallPieces s i n ms rs)

theorem subCallIsFinditer_proven : SubCallIsFinditer := by
  intro p e s f fuel
  induction fuel with
  | zero =>
    intro i k n st ms h
    simp [scanLoop] at h
  | succ fuel ih =>
    intro i k n st ms h
    rcases scan_step h with ⟨x, h1, rfl⟩ | ⟨st2, m, ms2, h1, h2, h3, rfl⟩
    · simp [subCallLoop, h1, subCallPieces, callAll, bind, Except.bind, pure, Except.pure]
    · have hsp := span0_of h2
      have hr := ih st2.ptr (k + 1) (n + 1) (nextSt st2) ms2 h3
      have hn : subCallLoop p e s f 0 fuel st2.ptr (n + 1) (k + 1)
          { st2 with mustAdvance := st2.ptr == st2.start, start := st2.ptr } =
          (do let rs ← callAll f (k + 1) ms2; return subCallPieces s st2.ptr (n + 1) ms2 rs) := hr
      rw [subCallLoop]
      simp only [ne_eq, not_true_eq_false, false_and, if_false, h1, h2, callAll, hn, bind, Except.bind,
        pure, Except.pure]
      cases f k m with
      | error x => rfl
      | ok r =>
        simp only
        cases callAll f (k + 1) ms2 with
        | error x => rfl
        | ok rs => cases r <;> simp [subCallPieces, hsp]

/-! ### `Match` -/

theorem getindex_lt {p : Pat} {m : MatchR} {g : GIdx} {i : Nat} (h : matchGetindex p m g = .ok i) :
    i < m.spans.length := by
  have hc : ∀ j : Int, (if j < 0 ∨ j ≥ m.spans.length then Except.error (.indexError "no such group")
      else (.ok j.toNat : Py Nat)) = .ok i → i < m.spans.length := by
    intro j hj
    by_cases h1 : j < 0 ∨ j ≥ m.spans.length
    · rw [if_pos h1] at hj
      cases hj
    · rw [if_neg h1] at hj
      cases hj
      omega
  unfold matchGetindex at h
  cases g with
  | int j => exact hc j h
  | name n =>
    simp only at h
    split at h
    · exact hc _ h
    · split at h
      · exact hc _ h
      · exact hc _ h
  | unhashable =>
    simp only at h
    split at h
    · exact hc _ h
    · cases h

/-- An integer group index is valid exactly when it is in range, however large: `match_getindex`
clips with `PyNumber_AsSsize_t(index, NULL)` and raises `IndexError`, not `OverflowError`. -/
def GroupIndexRange : Prop :=
  ∀ (p : Pat) (m : MatchR) (i : Int),
    matchGetindex p m (.int i) =
      if 0 ≤ i ∧ i < m.spans.length then .ok i.toNat else .error (.indexError "no such group")

theorem groupIndexRange_proven : GroupIndexRange := by
  intro p m i
  unfold matchGetindex
  by_cases h : 0 ≤ i ∧ i < m.spans.length
  · rw [if_pos h]
    simp only
    rw [if_neg (by omega)]
  · rw [if_neg h]
    simp only
    rw [if_pos (by omega)]

/-- `span`, `start`, `end`, `regs`, `group`, `[]` and `groups` say the same thing about a group, and
fail the same way. A group with no span reads as `-1` and `None`. For every index object. -/
def MatchMethodsAgree : Prop :=
  ∀ (p : Pat) (s : List Nat) (m : MatchR) (g : GIdx),
    (matchSpan p m g = (do return (← matchStart p m g, ← matchEnd p m g))) ∧
    (matchGroup p s m [g] = (do return .one (← matchGetslice p s m g))) ∧
    (∀ i, matchGetindex p m g = .ok i →
      (matchRegs m).getD i (0, 0) = markPair m i ∧
      matchGetslice p s m g = .ok (match m.spans.getD i none with
        | some x => .str (slice s x.1 x.2)
        | none => .none) ∧
      ((m.spans.getD i none).isNone → markPair m i = (-1, -1)) ∧
      (1 ≤ i → (matchGroups s m).getD (i - 1) .none = matchSlice s m i))

theorem matchMethodsAgree_proven : MatchMethodsAgree := by
  intro p s m g
  refine ⟨?_, rfl, fun i hi => ⟨?_, ?_, ?_, fun h1 => ?_⟩⟩
  · simp only [matchSpan, matchStart, matchEnd, bind, Except.bind, pure, Except.pure]
    cases matchGetindex p m g <;> rfl
  · have hlt := getindex_lt hi
    simp [matchRegs, List.getD_eq_getElem?_getD, hlt]
  · simp only [matchGetslice, bind, Except.bind, pure, Except.pure, hi, matchSlice]
    cases m.spans.getD i none with
    | none => rfl
    | some x => rfl
  · intro h1
    simp only [markPair]
    cases h2 : m.spans.getD i none with
    | none => rfl
    | some x =>
      rw [h2] at h1
      simp at h1
  · have hlt := getindex_lt hi
    have h2 : i - 1 < m.spans.length - 1 := by omega
    simp only [matchGroups, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2,
      Option.map_some, Option.getD_some]
    rw [show i - 1 + 1 = i by omega]

/-- `groupdict()[name]` is `group(name)`, and `lastgroup` names the group `lastindex` numbers. -/
def GroupdictAgrees : Prop :=
  ∀ (p : Pat) (s n : List Nat) (m : MatchR) (i : Nat),
    p.groupindex.lookup n = some i → i < m.spans.length →
    ((matchGroupdict p s m).lookup n = some (matchSlice s m i) ∧
      matchGetslice p s m (.name n) = .ok (matchSlice s m i))

theorem lookup_map {α : Type} (n : List Nat) (f : Nat → α) : ∀ (l : List (List Nat × Nat)) (i : Nat),
    l.lookup n = some i → (l.map fun x => (x.1, f x.2)).lookup n = some (f i) := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons x r ih =>
    intro i h
    obtain ⟨k, v⟩ := x
    simp only [List.lookup_cons, List.map_cons] at h ⊢
    by_cases hk : (n == k) = true
    · simp only [hk, Option.some.injEq] at h ⊢
      rw [h]
    · simp only [hk] at h ⊢
      exact ih i h

theorem groupdictAgrees_proven : GroupdictAgrees := by
  intro p s n m i h1 h2
  refine ⟨lookup_map n _ _ i h1, ?_⟩
  have hne : p.groupindex.isEmpty = false := by
    cases hg : p.groupindex with
    | nil => rw [hg] at h1; simp at h1
    | cons _ _ => rfl
  have hc : matchGetindex p m (.name n) = .ok i := by
    unfold matchGetindex
    simp only [hne, Bool.false_eq_true, if_false, h1]
    rw [if_neg (by omega)]
    simp
  simp only [matchGetslice, bind, Except.bind, pure, Except.pure, hc]

/-- `re.Scanner` treats a phrase as `re.compile` does: what the phrase matches is a token. -/
def ScannerAgreesCompile : Prop :=
  ∀ (ph s : List Nat), (matchSpans ph s false).isSome = true →
    (match scannerInit true [ph] 0 with
     | .ok c =>
       (match scan c [some 1] s with
        | .ok (r, _) => !r.isEmpty
        | .error _ => true)
     | .error _ => true) = true

theorem scannerAgreesCompile_refuted : ¬ScannerAgreesCompile := by
  intro h
  have := h [92, 119, 43] [233] (by decide +kernel)
  revert this
  decide +kernel

end PyLean.TextLibs.Re
