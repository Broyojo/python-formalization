import PyLean.TypeObj.TypeNew

/-!
The C3 linearization, stated as a specification independent of `pmerge`'s loop.

The C3 rule, as `Objects/typeobject.c:3426-3436` states it and the C3 paper defines it: take
the head of the *earliest* list whose head is in no list's tail, append it to the result,
remove it from every list, and repeat; succeed when every list is empty, fail when lists
remain and every head is in some tail. `C3Lin rests m` is that rule as an inductive relation:
it says nothing about indices, `remain[]`, `goto again` or `tail_contains`, and removes the
chosen class with `List.filter` from every list rather than advancing an index.

`pmerge_exact` proves that `pmerge` returns `.ok m` exactly when `C3Lin rests m`, and
`.conflict r` exactly when the rule gets stuck at `r` (`C3Reach rests r ∧ C3Stuck r`). Since
the rule is deterministic (`c3Pick_unique`), a merge that picks any other head (the last good
one, the first list's head, a list scanned from the end) or fails in any other state differs
from it on some input.
-/

namespace PyLean.TypeObj

section C3Spec

variable {α : Type} [DecidableEq α]

/-- `c` occurs in the tail of some list. -/
def InSomeTail (rests : List (List α)) (c : α) : Prop := ∃ r ∈ rests, c ∈ r.tail

/-- The head of `r`, if any, is in the tail of some list of `rests`. -/
def Blocked (rests : List (List α)) (r : List α) : Prop :=
  ∀ h, r.head? = some h → InSomeTail rests h

/-- The C3 choice: `c` heads the earliest list whose head is in no tail. -/
def C3Pick (rests : List (List α)) (c : α) : Prop :=
  ∃ pre t post, rests = pre ++ (c :: t) :: post ∧ ¬ InSomeTail rests c ∧
    ∀ r ∈ pre, Blocked rests r

/-- Remove `c` from every list. -/
def c3Remove (c : α) (rests : List (List α)) : List (List α) :=
  rests.map (List.filter (fun x => x != c))

/-- `C3Lin rests m`: the C3 rule linearizes `rests` to `m`. -/
inductive C3Lin : List (List α) → List α → Prop
  | done {rests : List (List α)} : (∀ r ∈ rests, r = []) → C3Lin rests []
  | step {rests : List (List α)} {c : α} {m : List α} :
      C3Pick rests c → C3Lin (c3Remove c rests) m → C3Lin rests (c :: m)

/-- The rule is stuck: some list is non-empty and every head is in some tail. -/
def C3Stuck (rests : List (List α)) : Prop :=
  (∃ r ∈ rests, r ≠ []) ∧ ∀ r ∈ rests, Blocked rests r

/-- States the rule reaches from `rests` by C3 steps. -/
inductive C3Reach : List (List α) → List (List α) → Prop
  | refl (rests : List (List α)) : C3Reach rests rests
  | step {rests r : List (List α)} {c : α} :
      C3Pick rests c → C3Reach (c3Remove c rests) r → C3Reach rests r

/-! ### `pmerge`'s scan is the C3 choice -/

theorem goodHead_iff (all : List (List α)) (c : α) :
    goodHead all c = true ↔ ¬ InSomeTail all c := by
  simp [goodHead, tailContains, InSomeTail]

theorem goodHead_false_iff (all : List (List α)) (c : α) :
    goodHead all c = false ↔ InSomeTail all c := by
  have := goodHead_iff all c
  cases h : goodHead all c <;> simp_all

theorem blocked_iff (all : List (List α)) (r : List α) :
    Blocked all r ↔ ∀ h, r.head? = some h → goodHead all h = false := by
  simp only [Blocked, goodHead_false_iff]

theorem candidateOf_some (all : List (List α)) :
    ∀ rests c, candidateOf all rests = some c →
      ∃ pre t post, rests = pre ++ (c :: t) :: post ∧ goodHead all c = true ∧
        ∀ r ∈ pre, Blocked all r := by
  intro rests
  induction rests with
  | nil => intro c h; simp [candidateOf] at h
  | cons r rest ih =>
    intro c h
    cases r with
    | nil =>
      obtain ⟨pre, t, post, h1, h2, h3⟩ := ih c (by simpa [candidateOf] using h)
      refine ⟨[] :: pre, t, post, by simp [h1], h2, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · intro x hx; simp at hx
      · exact h3 r hr
    | cons x xs =>
      simp only [candidateOf] at h
      by_cases hg : goodHead all x = true
      · simp only [hg, ite_true, Option.some.injEq] at h
        subst h
        exact ⟨[], xs, rest, rfl, hg, by simp⟩
      · simp only [hg, Bool.false_eq_true, ite_false] at h
        obtain ⟨pre, t, post, h1, h2, h3⟩ := ih c h
        refine ⟨(x :: xs) :: pre, t, post, by simp [h1], h2, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · intro y hy
          simp only [List.head?_cons, Option.some.injEq] at hy
          subst hy
          exact (goodHead_false_iff all x).mp (by simpa using hg)
        · exact h3 r hr

theorem candidateOf_of (all : List (List α)) (c : α) (t : List α) (post : List (List α))
    (hc : goodHead all c = true) :
    ∀ pre, (∀ r ∈ pre, Blocked all r) → candidateOf all (pre ++ (c :: t) :: post) = some c := by
  intro pre
  induction pre with
  | nil => intro _; simp [candidateOf, hc]
  | cons r rest ih =>
    intro hb
    have hr := hb r List.mem_cons_self
    have hrest := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    cases r with
    | nil => simpa [candidateOf] using hrest
    | cons x xs =>
      have hx : goodHead all x = false := (blocked_iff all _).mp hr x rfl
      simp [candidateOf, hx, hrest]

theorem candidateOf_none (all : List (List α)) :
    ∀ rests, candidateOf all rests = none ↔ ∀ r ∈ rests, Blocked all r := by
  intro rests
  induction rests with
  | nil => simp [candidateOf]
  | cons r rest ih =>
    cases r with
    | nil =>
      simp only [candidateOf, ih, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h; exact ⟨fun x hx => by simp at hx, h⟩
      · intro h; exact h.2
    | cons x xs =>
      simp only [candidateOf, List.mem_cons, forall_eq_or_imp]
      by_cases hg : goodHead all x = true
      · simp only [hg, ite_true, reduceCtorEq, false_iff, not_and]
        intro hb
        exact absurd ((blocked_iff all _).mp hb x rfl) (by simp [hg])
      · simp only [hg, Bool.false_eq_true, ite_false, ih]
        constructor
        · intro h
          refine ⟨?_, h⟩
          intro y hy
          simp only [List.head?_cons, Option.some.injEq] at hy
          subst hy
          exact (goodHead_false_iff all x).mp (by simpa using hg)
        · intro h; exact h.2

theorem c3Pick_of_candidate (rests : List (List α)) (c : α)
    (h : candidateOf rests rests = some c) : C3Pick rests c := by
  obtain ⟨pre, t, post, h1, h2, h3⟩ := candidateOf_some rests rests c h
  exact ⟨pre, t, post, h1, (goodHead_iff rests c).mp h2, h3⟩

theorem candidate_of_c3Pick (rests : List (List α)) (c : α) (h : C3Pick rests c) :
    candidateOf rests rests = some c := by
  obtain ⟨pre, t, post, h1, h2, h3⟩ := h
  have hg : goodHead rests c = true := (goodHead_iff rests c).mpr h2
  have := candidateOf_of rests c t post hg pre h3
  rw [← h1] at this
  exact this

/-- The C3 choice is unique. -/
theorem c3Pick_unique (rests : List (List α)) (c c' : α) (h : C3Pick rests c)
    (h' : C3Pick rests c') : c = c' := by
  have := candidate_of_c3Pick rests c h
  rw [candidate_of_c3Pick rests c' h'] at this
  exact (Option.some.inj this).symm

theorem c3Pick_mem (rests : List (List α)) (c : α) (h : C3Pick rests c) :
    ∃ t, (c :: t) ∈ rests := by
  obtain ⟨pre, t, post, h1, _, _⟩ := h
  exact ⟨t, by rw [h1]; simp⟩

theorem advance1_eq_filter (c : α) (r : List α) (h : c ∉ r.tail) :
    advance1 c r = r.filter (fun x => x != c) := by
  cases r with
  | nil => rfl
  | cons x t =>
    have ht : c ∉ t := by simpa using h
    have hf : t.filter (fun x => x != c) = t := by
      apply List.filter_eq_self.mpr
      intro a ha
      have : a ≠ c := fun hac => ht (hac ▸ ha)
      simpa using this
    by_cases hx : x = c
    · subst hx; simp [advance1, hf]
    · simp [advance1, hx, hf]

/-- Advancing `remain[j]` where list `j` is headed by the candidate removes the candidate from
every list, because it is in no tail. -/
theorem advance_eq_c3Remove (c : α) (rests : List (List α)) (h : ¬ InSomeTail rests c) :
    advance c rests = c3Remove c rests := by
  unfold advance c3Remove
  apply List.map_congr_left
  intro r hr
  exact advance1_eq_filter c r (fun hc => h ⟨r, hr, hc⟩)

theorem c3Pick_not_stuck (rests : List (List α)) (c : α) (h : C3Pick rests c) :
    ¬ C3Stuck rests := by
  intro hs
  obtain ⟨pre, t, post, h1, h2, _⟩ := h
  have hm : (c :: t) ∈ rests := by rw [h1]; simp
  exact h2 (hs.2 _ hm c rfl)

/-! ### Soundness and completeness -/

theorem pmerge_sound_ok (fuel : Nat) (rests : List (List α)) (m : List α)
    (h : pmerge fuel rests = .ok m) : C3Lin rests m := by
  induction fuel generalizing rests m with
  | zero => simp [pmerge] at h
  | succ n ih =>
    rcases pmerge_succ_ok n rests m h with ⟨c, m', hc, hm', rfl⟩ | ⟨hall, rfl⟩
    · have hp := c3Pick_of_candidate rests c hc
      have hnt : ¬ InSomeTail rests c := by
        obtain ⟨_, _, _, _, h2, _⟩ := hp; exact h2
      refine C3Lin.step hp ?_
      rw [← advance_eq_c3Remove c rests hnt]
      exact ih _ _ hm'
    · refine C3Lin.done ?_
      intro r hr
      have := (List.all_eq_true.mp hall) r hr
      simpa using this

theorem pmerge_complete (rests : List (List α)) (m : List α) (h : C3Lin rests m) :
    ∀ fuel, totalLen rests < fuel → pmerge fuel rests = .ok m := by
  induction h with
  | @done rests hall =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ n =>
      have hnone : candidateOf rests rests = none := by
        rw [candidateOf_none]
        intro r hr x hx
        rw [hall r hr] at hx
        simp at hx
      have hall' : rests.all List.isEmpty = true := by
        apply List.all_eq_true.mpr
        intro r hr
        simp [hall r hr]
      simp [pmerge, hnone, hall']
  | @step rests c m hp _ ih =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ n =>
      have hc := candidate_of_c3Pick rests c hp
      have hnt : ¬ InSomeTail rests c := by
        obtain ⟨_, _, _, _, h2, _⟩ := hp; exact h2
      obtain ⟨t, ht⟩ := c3Pick_mem rests c hp
      have hlt := totalLen_advance_lt c rests t ht
      rw [advance_eq_c3Remove c rests hnt] at hlt
      have hrec := ih n (by omega)
      simp only [pmerge, hc]
      rw [advance_eq_c3Remove c rests hnt, hrec]

theorem pmerge_sound_conflict (fuel : Nat) (rests r : List (List α))
    (h : pmerge fuel rests = .conflict r) : C3Reach rests r ∧ C3Stuck r := by
  induction fuel generalizing rests with
  | zero => simp [pmerge] at h
  | succ n ih =>
    simp only [pmerge] at h
    cases hc : candidateOf rests rests with
    | some c =>
      rw [hc] at h
      simp only at h
      have hp := c3Pick_of_candidate rests c hc
      have hnt : ¬ InSomeTail rests c := by
        obtain ⟨_, _, _, _, h2, _⟩ := hp; exact h2
      cases hq : pmerge n (advance c rests) with
      | ok m => rw [hq] at h; simp at h
      | fuel => rw [hq] at h; simp at h
      | conflict r' =>
        rw [hq] at h
        simp only [Merge.conflict.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih _ hq
        rw [advance_eq_c3Remove c rests hnt] at h1
        exact ⟨C3Reach.step hp h1, h2⟩
    | none =>
      rw [hc] at h
      simp only at h
      by_cases ha : rests.all List.isEmpty = true
      · simp [ha] at h
      · simp only [ha, Bool.false_eq_true, ite_false, Merge.conflict.injEq] at h
        subst h
        refine ⟨C3Reach.refl _, ?_, (candidateOf_none rests rests).mp hc⟩
        refine Classical.byContradiction fun hne => ha ?_
        apply List.all_eq_true.mpr
        intro x hx
        by_cases hx' : x = []
        · simp [hx']
        · exact absurd ⟨x, hx, hx'⟩ hne

theorem c3Lin_cons (rests : List (List α)) (c : α) (m : List α) (h : C3Lin rests (c :: m)) :
    C3Pick rests c ∧ C3Lin (c3Remove c rests) m := by
  cases h with
  | step hp hl => exact ⟨hp, hl⟩

theorem c3Lin_nil (rests : List (List α)) (h : C3Lin rests []) : ∀ r ∈ rests, r = [] := by
  cases h with
  | done hall => exact hall

/-- A stuck state reached from `rests` rules out every linearization of `rests`. -/
theorem c3_stuck_no_lin (rests r : List (List α)) (h : C3Reach rests r) (hs : C3Stuck r) :
    ∀ m, ¬ C3Lin rests m := by
  induction h with
  | refl rests =>
    intro m hl
    cases m with
    | nil =>
      obtain ⟨x, hx, hne⟩ := hs.1
      exact hne (c3Lin_nil _ hl x hx)
    | cons c m => exact c3Pick_not_stuck _ c (c3Lin_cons _ c m hl).1 hs
  | @step rests r c hp _ ih =>
    intro m hl
    cases m with
    | nil =>
      obtain ⟨t, ht⟩ := c3Pick_mem rests c hp
      have := c3Lin_nil _ hl _ ht
      simp at this
    | cons c' m =>
      obtain ⟨hp', hl'⟩ := c3Lin_cons _ c' m hl
      have := c3Pick_unique rests c c' hp hp'
      subst this
      exact ih hs m hl'

/-- The stuck state the rule reaches is unique. -/
theorem c3_reach_unique (rests r1 r2 : List (List α)) (h1 : C3Reach rests r1) (hs1 : C3Stuck r1)
    (h2 : C3Reach rests r2) (hs2 : C3Stuck r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | refl rests =>
    cases h2 with
    | refl => rfl
    | step hp _ => exact absurd hs1 (c3Pick_not_stuck _ _ hp)
  | @step rests r c hp _ ih =>
    cases h2 with
    | refl => exact absurd hs2 (c3Pick_not_stuck _ _ hp)
    | step hp' h2' =>
      have := c3Pick_unique _ _ _ hp hp'
      subst this
      exact ih r2 hs1 h2' hs2

/-- **`pmerge` is exactly the C3 rule.** With the fuel `c3Merge` gives it, `pmerge` returns
`.ok m` exactly when the rule linearizes the lists to `m`, and `.conflict r` exactly when the
rule gets stuck at `r`. -/
theorem pmerge_exact (rests : List (List α)) :
    (∀ m, pmerge (totalLen rests + 1) rests = .ok m ↔ C3Lin rests m) ∧
    (∀ r, pmerge (totalLen rests + 1) rests = .conflict r ↔ C3Reach rests r ∧ C3Stuck r) := by
  refine ⟨fun m => ⟨pmerge_sound_ok _ rests m, fun h => pmerge_complete rests m h _ (by omega)⟩,
    fun r => ⟨pmerge_sound_conflict _ rests r, ?_⟩⟩
  rintro ⟨h1, h2⟩
  cases hp : pmerge (totalLen rests + 1) rests with
  | ok m => exact absurd (pmerge_sound_ok _ rests m hp) (c3_stuck_no_lin rests r h1 h2 m)
  | conflict r' =>
    obtain ⟨h1', h2'⟩ := pmerge_sound_conflict _ rests r' hp
    rw [c3_reach_unique rests r r' h1 h2 h1' h2']
  | fuel => exact absurd hp (pmerge_total _ rests (by omega))

/-! ### `check_duplicates` -/

/-- `d` is the first item of `l` that occurs again later: every earlier item occurs once. -/
def IsFirstDup (l : List α) (d : α) : Prop :=
  ∃ pre post, l = pre ++ d :: post ∧ d ∈ post ∧ pre.Nodup ∧ ∀ x ∈ pre, x ∉ d :: post

theorem firstDuplicate_none_iff (l : List α) : firstDuplicate l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [firstDuplicate]
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp [firstDuplicate, hx]
    · simp [firstDuplicate, hx, ih]

theorem firstDuplicate_some_iff (l : List α) (d : α) :
    firstDuplicate l = some d ↔ IsFirstDup l d := by
  induction l with
  | nil =>
    simp only [firstDuplicate, reduceCtorEq, false_iff]
    rintro ⟨pre, post, h, _⟩
    cases pre <;> simp at h
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · have hfd : firstDuplicate (x :: xs) = some x := by simp [firstDuplicate, hx]
      rw [hfd]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[], xs, rfl, hx, List.nodup_nil, by simp⟩
      · rintro ⟨pre, post, h1, h2, h3, h4⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h1
          rw [h1.1]
        | cons y pre' =>
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exfalso
          have hy : x ∉ pre' := (List.nodup_cons.mp h3).1
          have hy2 : x ∉ d :: post := h4 x List.mem_cons_self
          simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hy hx
          · exact hy2 hx
    · have hfd : firstDuplicate (x :: xs) = firstDuplicate xs := by simp [firstDuplicate, hx]
      rw [hfd, ih]
      constructor
      · rintro ⟨pre, post, h1, h2, h3, h4⟩
        refine ⟨x :: pre, post, by simp [h1], h2, ?_, ?_⟩
        · refine List.nodup_cons.mpr ⟨?_, h3⟩
          intro hm; exact hx (by rw [h1]; simp [hm])
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · intro hm; exact hx (by rw [h1]; simp_all)
          · exact h4 y hy
      · rintro ⟨pre, post, h1, h2, h3, h4⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact absurd h2 hx
        | cons y pre' =>
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact ⟨pre', post, rfl, h2, (List.nodup_cons.mp h3).2,
            fun z hz => h4 z (List.mem_cons_of_mem _ hz)⟩

/-! ### `mro_implementation_unlocked` -/

theorem firstIncomplete_at (baseMro : α → Option (List α)) (b : α) (post : List α)
    (hb : baseMro b = none) :
    ∀ pre, (∀ x ∈ pre, baseMro x ≠ none) → firstIncomplete baseMro (pre ++ b :: post) = some b := by
  intro pre
  induction pre with
  | nil => intro _; simp [firstIncomplete, hb]
  | cons x xs ih =>
    intro h
    have hx := h x List.mem_cons_self
    cases hm : baseMro x with
    | none => exact absurd hm hx
    | some m =>
      simp only [List.cons_append, firstIncomplete, hm]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem firstIncomplete_none_of (baseMro : α → Option (List α)) :
    ∀ bases : List α, (∀ x ∈ bases, baseMro x ≠ none) → firstIncomplete baseMro bases = none := by
  intro bases
  induction bases with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    cases hm : baseMro x with
    | none => exact absurd hm (h x List.mem_cons_self)
    | some m =>
      simp only [firstIncomplete, hm]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

end C3Spec

/-- **C3 is the rule, and nothing else.** For every list of lists of classes, `pmerge`
(`Objects/typeobject.c:3401-3469`, with `tail_contains` at `:3286`) returns the merge exactly
when the C3 rule (`C3Lin`: the head of the earliest list whose head is in no tail, removed
from every list) linearizes the lists to it, and fails with remaining lists `r` exactly when
the rule gets stuck at `r`. Source: the comment at `:3431-3436` ("choose the class which
appears in the MRO of the earliest direct superclass") and the C3 paper it cites (`:3259`). -/
def C3MergeExact : Prop :=
  ∀ (rests : List (List Addr)),
    (∀ m, pmerge (totalLen rests + 1) rests = .ok m ↔ C3Lin rests m) ∧
    (∀ r, pmerge (totalLen rests + 1) rests = .conflict r ↔ C3Reach rests r ∧ C3Stuck r)

theorem c3MergeExact_proven : C3MergeExact := fun rests => pmerge_exact rests

/-- **`check_duplicates` finds the first repeated base.** `firstDuplicate l` is `none` exactly
when `l` has no repeat, and is `some d` exactly when `d` is the first item of `l` that occurs
again later, the `o` of `Objects/typeobject.c:3318-3321`. -/
def CheckDuplicatesExact : Prop :=
  ∀ (l : List Addr), (firstDuplicate l = none ↔ l.Nodup) ∧
    ∀ d, firstDuplicate l = some d ↔ IsFirstDup l d

theorem checkDuplicatesExact_proven : CheckDuplicatesExact := fun l =>
  ⟨firstDuplicate_none_iff l, fun d => firstDuplicate_some_iff l d⟩

/-- **`mro_implementation_unlocked`, every branch.** `Objects/typeobject.c:3471-3556`:
* the first base whose `tp_mro` is NULL is reported, before any other check (`:3480-3491`),
  for one base as for several;
* with one base the MRO is the class followed by the base's MRO (`:3493-3513`);
* otherwise a repeated base is reported (the first one, `check_duplicates`, `:3516`);
* otherwise the result is the class followed by the C3 merge of the bases' MROs and the
  tuple of bases (`to_merge`, `:3535-3541`), or a conflict at the state where the rule is
  stuck. -/
def MroImplementationExact : Prop :=
  ∀ (self : Addr) (baseMro : Addr → Option (List Addr)) (bases : List Addr),
    (∀ pre b post, bases = pre ++ b :: post → baseMro b = none →
      (∀ x ∈ pre, baseMro x ≠ none) → mroImpl self baseMro bases = .incomplete b) ∧
    ((∀ x ∈ bases, baseMro x ≠ none) →
      (∀ b, bases = [b] → mroImpl self baseMro bases = .ok (self :: (baseMro b).getD [])) ∧
      (bases.length ≠ 1 → ∀ d, IsFirstDup bases d → mroImpl self baseMro bases = .duplicate d) ∧
      (bases.length ≠ 1 → bases.Nodup →
        let tm := bases.map (fun b => (baseMro b).getD []) ++ [bases]
        (∀ mro, mroImpl self baseMro bases = .ok mro ↔ ∃ m, mro = self :: m ∧ C3Lin tm m) ∧
        (∀ r, mroImpl self baseMro bases = .conflict r ↔ C3Reach tm r ∧ C3Stuck r)))

theorem mroImpl_multi (self : Addr) (baseMro : Addr → Option (List Addr)) (bases : List Addr)
    (hc : ∀ x ∈ bases, baseMro x ≠ none) (hl : bases.length ≠ 1) :
    mroImpl self baseMro bases = c3Merge self baseMro bases := by
  have hn := firstIncomplete_none_of baseMro bases hc
  unfold mroImpl
  rw [hn]
  match bases, hl with
  | [], _ => rfl
  | [_], hl => simp at hl
  | _ :: _ :: _, _ => rfl

theorem mroImplementationExact_proven : MroImplementationExact := by
  intro self baseMro bases
  refine ⟨?_, ?_⟩
  · intro pre b post h hb hpre
    have := firstIncomplete_at baseMro b post hb pre hpre
    rw [← h] at this
    simp [mroImpl, this]
  · intro hc
    have hn := firstIncomplete_none_of baseMro bases hc
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      subst hb
      simp [mroImpl, hn]
    · intro hl d hd
      rw [mroImpl_multi self baseMro bases hc hl]
      have := (firstDuplicate_some_iff bases d).mpr hd
      simp [c3Merge, this]
    · intro hl hnd
      rw [mroImpl_multi self baseMro bases hc hl]
      have hfd := (firstDuplicate_none_iff bases).mpr hnd
      have hex := pmerge_exact (toMerge baseMro bases)
      simp only [toMerge] at hex
      refine ⟨?_, ?_⟩
      · intro mro
        simp only [c3Merge, hfd, toMerge]
        constructor
        · intro h
          split at h
          · rename_i m hm
            simp only [Lin.ok.injEq] at h
            exact ⟨m, h.symm, (hex.1 m).mp hm⟩
          · simp at h
          · simp at h
        · rintro ⟨m, rfl, hm⟩
          rw [(hex.1 m).mpr hm]
      · intro r
        simp only [c3Merge, hfd, toMerge]
        constructor
        · intro h
          split at h
          · simp at h
          · rename_i r' hr
            simp only [Lin.conflict.injEq] at h
            subst h
            exact (hex.2 r').mp hr
          · simp at h
        · intro h
          rw [(hex.2 r).mpr h]

/-! ### Worked examples, checked against CPython 3.15.2 -/

/-- `class X: pass; class Y: pass; class B(X): pass; class C(Y): pass; class D(B, C): pass`
gives `D.__mro__ == (D, B, X, C, Y, object)`: after `B`, `X` (from the earliest base's MRO)
is chosen before `C`, the rule of `Objects/typeobject.c:3431-3436`. A merge that scanned the
lists from the end would give `D B C Y X object`. Addresses: object 0, X 1, Y 2, B 3, C 4,
D 5. -/
def C3ExampleEarliestBase : Prop :=
  mroImpl (5 : Addr)
    (fun b => if b = 1 then some [1, 0] else if b = 2 then some [2, 0]
      else if b = 3 then some [3, 1, 0] else if b = 4 then some [4, 2, 0] else none)
    [3, 4] = .ok [5, 3, 1, 4, 2, 0]

theorem c3ExampleEarliestBase_proven : C3ExampleEarliestBase := by rfl

/-- `class X2(A, B2)`, `class Y2(B2, A)`, `type('Z', (X2, Y2), {})` fails, stuck with heads
`A` and `B2` (CPython: "Cannot create a consistent method resolution order (MRO) for bases
A, B2"). Addresses: object 0, A 1, B2 2, X2 3, Y2 4, Z 5. -/
def C3ExampleConflict : Prop :=
  mroImpl (5 : Addr)
    (fun b => if b = 1 then some [1, 0] else if b = 2 then some [2, 0]
      else if b = 3 then some [3, 1, 2, 0] else if b = 4 then some [4, 2, 1, 0] else none)
    [3, 4] = .conflict [[1, 2, 0], [2, 1, 0], []]

theorem c3ExampleConflict_proven : C3ExampleConflict := by rfl

end PyLean.TypeObj
