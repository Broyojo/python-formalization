import PyLean.TypeObj.Protocol

/-!
C3 linearization: `tail_contains`, `pmerge`, `mro_implementation_unlocked`
(`Objects/typeobject.c:3286-3556`).

The C code keeps an index `remain[i]` into each list of `to_merge`. Here the state is the
list of remaining suffixes, `rests[i] = to_merge[i][remain[i]:]`, so:

* `remain[i] >= PyTuple_GET_SIZE(cur)` is `rests[i] = []`;
* `tail_contains(lst, remain[j], c)` is `c ∈ rests[j].tail`;
* the candidate `PyTuple_GET_ITEM(cur, remain[i])` is `rests[i].head`.

The merge is generic in the class type `α`, so the proofs say nothing about classes
beyond decidable identity.
-/

namespace PyLean.TypeObj

variable {α : Type} [DecidableEq α]

/-- `tail_contains(lst, remain, c)`, `Objects/typeobject.c:3286`. -/
def tailContains (rest : List α) (c : α) : Bool := rest.tail.contains c

/-- The inner test at `Objects/typeobject.c:3439-3443`: `c` is in no tail. -/
def goodHead (rests : List (List α)) (c : α) : Bool :=
  !rests.any (fun r => tailContains r c)

/-- The scan of `Objects/typeobject.c:3421-3457`: the first list whose head is in no
tail. -/
def candidateOf (all : List (List α)) : List (List α) → Option α
  | [] => none
  | [] :: rest => candidateOf all rest
  | (c :: _) :: rest => if goodHead all c then some c else candidateOf all rest

/-- `remain[j]++` when list `j` is headed by the candidate, `:3448-3454`. -/
def advance1 (c : α) : List α → List α
  | [] => []
  | x :: t => if x = c then t else x :: t

/-- `remain[j]++` for every list headed by the candidate. -/
def advance (c : α) (rests : List (List α)) : List (List α) := rests.map (advance1 c)

/-- Result of `pmerge`. -/
inductive Merge (α : Type) where
  | ok (merged : List α)
  /-- `set_mro_error`: no candidate although some list is non-empty. The argument holds
  the remaining suffixes. -/
  | conflict (rests : List (List α))
  | fuel

/-- `pmerge`, `Objects/typeobject.c:3401`, the `goto again` loop by fuel. -/
def pmerge : Nat → List (List α) → Merge α
  | 0, _ => .fuel
  | fuel + 1, rests =>
    match candidateOf rests rests with
    | some c =>
      match pmerge fuel (advance c rests) with
      | .ok m => .ok (c :: m)
      | r => r
    | none => if rests.all List.isEmpty then .ok [] else .conflict rests

/-- Number of items left to merge. -/
def totalLen (rests : List (List α)) : Nat := (rests.map List.length).sum

/-! ### The candidate is a head, and merging terminates -/

theorem candidateOf_isHead (all : List (List α)) :
    ∀ rests c, candidateOf all rests = some c → ∃ t, (c :: t) ∈ rests := by
  intro rests
  induction rests with
  | nil => intro c h; simp [candidateOf] at h
  | cons r rest ih =>
    intro c h
    cases r with
    | nil =>
      obtain ⟨t, ht⟩ := ih c (by simpa [candidateOf] using h)
      exact ⟨t, List.mem_cons_of_mem _ ht⟩
    | cons x xs =>
      simp only [candidateOf] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨xs, List.mem_cons_self⟩
      · obtain ⟨t, ht⟩ := ih c h
        exact ⟨t, List.mem_cons_of_mem _ ht⟩

theorem candidateOf_good (all : List (List α)) :
    ∀ rests c, candidateOf all rests = some c → goodHead all c = true := by
  intro rests
  induction rests with
  | nil => intro c h; simp [candidateOf] at h
  | cons r rest ih =>
    intro c h
    cases r with
    | nil => exact ih c (by simpa [candidateOf] using h)
    | cons x xs =>
      simp only [candidateOf] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        exact hg
      · exact ih c h

theorem totalLen_advance_le (c : α) (rests : List (List α)) :
    totalLen (advance c rests) ≤ totalLen rests := by
  induction rests with
  | nil => simp [totalLen, advance]
  | cons r rest ih =>
    simp only [totalLen, advance, List.map_cons, List.sum_cons] at ih ⊢
    cases r with
    | nil => simpa [advance1] using ih
    | cons x xs =>
      by_cases hx : x = c
      · simp only [advance1, hx, ite_true, List.length_cons]
        omega
      · simp only [advance1, hx, ite_false, List.length_cons]
        omega

theorem totalLen_advance_lt (c : α) (rests : List (List α)) (t : List α)
    (h : (c :: t) ∈ rests) : totalLen (advance c rests) < totalLen rests := by
  induction rests with
  | nil => simp at h
  | cons r rest ih =>
    have hle := totalLen_advance_le c rest
    simp only [totalLen, advance, List.map_cons, List.sum_cons] at ih hle ⊢
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1
      simp only [advance1, ite_true, List.length_cons]
      omega
    · have := ih h1
      cases r with
      | nil => simpa [advance1] using this
      | cons x xs =>
        by_cases hx : x = c
        · simp only [advance1, hx, ite_true, List.length_cons]
          omega
        · simp only [advance1, hx, ite_false, List.length_cons]
          omega

/-- What a successful `pmerge` step did. -/
theorem pmerge_succ_ok (n : Nat) (rests : List (List α)) (m : List α)
    (h : pmerge (n + 1) rests = .ok m) :
    (∃ c m', candidateOf rests rests = some c ∧ pmerge n (advance c rests) = .ok m' ∧
      m = c :: m') ∨ (rests.all List.isEmpty = true ∧ m = []) := by
  simp only [pmerge] at h
  cases hc : candidateOf rests rests with
  | some c =>
    rw [hc] at h
    simp only at h
    cases hp : pmerge n (advance c rests) with
    | ok m' =>
      rw [hp] at h
      simp only [Merge.ok.injEq] at h
      exact Or.inl ⟨c, m', rfl, hp, h.symm⟩
    | conflict r => rw [hp] at h; simp at h
    | fuel => rw [hp] at h; simp at h
  | none =>
    rw [hc] at h
    simp only at h
    by_cases ha : rests.all List.isEmpty = true
    · simp only [ha, ite_true] at h
      simp only [Merge.ok.injEq] at h
      exact Or.inr ⟨ha, h.symm⟩
    · simp only [ha, ite_false] at h
      simp at h

/-- Merging never runs out of fuel when fuel exceeds the number of items. -/
theorem pmerge_total (fuel : Nat) (rests : List (List α)) (h : totalLen rests < fuel) :
    pmerge fuel rests ≠ .fuel := by
  induction fuel generalizing rests with
  | zero => omega
  | succ n ih =>
    intro hm
    simp only [pmerge] at hm
    cases hc : candidateOf rests rests with
    | some c =>
      rw [hc] at hm
      simp only at hm
      obtain ⟨t, ht⟩ := candidateOf_isHead rests rests c hc
      have hlt := totalLen_advance_lt c rests t ht
      have hne := ih (advance c rests) (by omega)
      cases hp : pmerge n (advance c rests) with
      | ok m' => rw [hp] at hm; simp at hm
      | conflict r => rw [hp] at hm; simp at hm
      | fuel => exact hne hp
    | none =>
      rw [hc] at hm
      simp only at hm
      split at hm <;> simp at hm

/-! ### Order preservation -/

/-- A merge result extends each input without reordering it: the core of both the
local-precedence and the monotonicity constraint of C3. -/
theorem pmerge_sublist (fuel : Nat) (rests : List (List α)) (m : List α)
    (h : pmerge fuel rests = .ok m) : ∀ r ∈ rests, r.Sublist m := by
  induction fuel generalizing rests m with
  | zero => simp [pmerge] at h
  | succ n ih =>
    rcases pmerge_succ_ok n rests m h with ⟨c, m', _, hm', rfl⟩ | ⟨hall, rfl⟩
    · intro r hr
      have hs := ih _ m' hm' (advance1 c r) (List.mem_map_of_mem hr)
      cases r with
      | nil => simp
      | cons x t =>
        by_cases hx : x = c
        · simp only [advance1, hx, ite_true] at hs
          rw [hx]
          exact hs.cons₂ c
        · simp only [advance1, hx, ite_false] at hs
          exact hs.cons c
    · intro r hr
      have := (List.all_eq_true.mp hall) r hr
      simp only [List.isEmpty_iff] at this
      subst this
      simp

/-- Every merged class comes from an input list. -/
theorem pmerge_mem (fuel : Nat) (rests : List (List α)) (m : List α)
    (h : pmerge fuel rests = .ok m) : ∀ x ∈ m, ∃ r ∈ rests, x ∈ r := by
  induction fuel generalizing rests m with
  | zero => simp [pmerge] at h
  | succ n ih =>
    rcases pmerge_succ_ok n rests m h with ⟨c, m', hc, hm', rfl⟩ | ⟨_, rfl⟩
    · intro x hx
      rcases List.mem_cons.mp hx with h1 | h1
      · subst h1
        obtain ⟨t, ht⟩ := candidateOf_isHead rests rests x hc
        exact ⟨_, ht, List.mem_cons_self⟩
      · obtain ⟨r, hr, hxr⟩ := ih _ _ hm' x h1
        simp only [advance, List.mem_map] at hr
        obtain ⟨r0, hr0, rfl⟩ := hr
        refine ⟨r0, hr0, ?_⟩
        cases r0 with
        | nil => simp [advance1] at hxr
        | cons y t =>
          by_cases hy : y = c
          · simp only [advance1, hy, ite_true] at hxr
            simp [hy, hxr]
          · simpa [advance1, hy] using hxr
    · simp

/-- After a good candidate is taken, it is in no remaining list, provided lists are
duplicate-free at its head (it is in no tail). -/
theorem not_mem_advance (c : α) (rests : List (List α))
    (hgood : goodHead rests c = true) :
    ∀ r ∈ advance c rests, c ∉ r := by
  intro r hr
  simp only [advance, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have hnotTail : tailContains r0 c = false := by
    simp only [goodHead, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hgood
    simpa using hgood r0 hr0
  cases r0 with
  | nil => simp [advance1]
  | cons y t =>
    have ht : c ∉ t := by simpa [tailContains] using hnotTail
    by_cases hy : y = c
    · simpa [advance1, hy] using ht
    · simp only [advance1, hy, ite_false, List.mem_cons, not_or]
      exact ⟨fun h => hy h.symm, ht⟩

theorem advance_nodup (c : α) (rests : List (List α)) (hnd : ∀ r ∈ rests, r.Nodup) :
    ∀ r ∈ advance c rests, r.Nodup := by
  intro r hr
  simp only [advance, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have h := hnd r0 hr0
  cases r0 with
  | nil => simp [advance1]
  | cons y t =>
    by_cases hy : y = c
    · simp only [advance1, hy, ite_true]
      exact (List.nodup_cons.mp (by simpa [hy] using h)).2
    · simpa [advance1, hy] using h

/-- A merge of duplicate-free lists is duplicate-free. -/
theorem pmerge_nodup (fuel : Nat) (rests : List (List α)) (m : List α)
    (h : pmerge fuel rests = .ok m) (hnd : ∀ r ∈ rests, r.Nodup) : m.Nodup := by
  induction fuel generalizing rests m with
  | zero => simp [pmerge] at h
  | succ n ih =>
    rcases pmerge_succ_ok n rests m h with ⟨c, m', hc, hm', rfl⟩ | ⟨_, rfl⟩
    · have hnd' := advance_nodup c rests hnd
      have hgood := candidateOf_good rests rests c hc
      have hrec := ih _ _ hm' hnd'
      refine List.nodup_cons.mpr ⟨?_, hrec⟩
      intro hcm
      obtain ⟨r, hr, hcr⟩ := pmerge_mem n _ _ hm' c hcm
      exact not_mem_advance c rests hgood r hr hcr
    · simp

/-! ### Linearization -/

/-- The result of `mro_implementation_unlocked`, `Objects/typeobject.c:3471`, for a class
`self` given its bases and the MRO of each base. `duplicate` is `check_duplicates`.
`baseMro b = none` is `lookup_tp_mro(base) == NULL`. -/
inductive Lin (α : Type) where
  | ok (mro : List α)
  | incomplete (base : α)
  | duplicate (base : α)
  | conflict (rests : List (List α))
  | fuel

/-- The first repeated item of a list, `check_duplicates`, `Objects/typeobject.c:3310`. -/
def firstDuplicate : List α → Option α
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDuplicate xs

/-- The first base without an MRO, the check at `Objects/typeobject.c:3482-3491`. -/
def firstIncomplete (baseMro : α → Option (List α)) : List α → Option α
  | [] => none
  | b :: bs =>
    match baseMro b with
    | none => some b
    | some _ => firstIncomplete baseMro bs

/-- The list `to_merge`, `Objects/typeobject.c:3535-3541`. -/
def toMerge (baseMro : α → Option (List α)) (bases : List α) : List (List α) :=
  bases.map (fun b => (baseMro b).getD []) ++ [bases]

/-- The slow path alone: `check_duplicates` and `pmerge`. -/
def c3Merge (self : α) (baseMro : α → Option (List α)) (bases : List α) : Lin α :=
  match firstDuplicate bases with
  | some d => .duplicate d
  | none =>
    let rests := toMerge baseMro bases
    match pmerge (totalLen rests + 1) rests with
    | .ok m => .ok (self :: m)
    | .conflict r => .conflict r
    | .fuel => .fuel

/-- `mro_implementation_unlocked`, `Objects/typeobject.c:3471`. -/
def mroImpl (self : α) (baseMro : α → Option (List α)) (bases : List α) : Lin α :=
  match firstIncomplete baseMro bases with
  | some b => .incomplete b
  | none =>
    match bases with
    | [b] => .ok (self :: (baseMro b).getD [])
    | _ => c3Merge self baseMro bases

theorem firstIncomplete_none (baseMro : α → Option (List α)) (bases : List α)
    (h : firstIncomplete baseMro bases = none) :
    ∀ b ∈ bases, ∃ m, baseMro b = some m := by
  induction bases with
  | nil => simp
  | cons b bs ih =>
    simp only [firstIncomplete] at h
    split at h
    · simp at h
    · rename_i m hm
      intro x hx
      rcases List.mem_cons.mp hx with h1 | h1
      · subst h1; exact ⟨m, hm⟩
      · exact ih h x h1

/-- `pmerge` of one duplicate-free list and an empty list returns the list. -/
theorem pmerge_single (l : List α) (hnd : l.Nodup) (fuel : Nat) (hf : l.length < fuel) :
    pmerge fuel [l, []] = .ok l := by
  induction l generalizing fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ n => simp [pmerge, candidateOf]
  | cons y ys ih =>
    cases fuel with
    | zero => omega
    | succ n =>
      have hy : y ∉ ys := (List.nodup_cons.mp hnd).1
      have hgood : goodHead [y :: ys, []] y = true := by
        simp [goodHead, tailContains, hy]
      have hadv : advance y [y :: ys, []] = [ys, []] := by simp [advance, advance1]
      simp only [pmerge, candidateOf, hgood, ite_true, hadv]
      rw [ih (List.nodup_cons.mp hnd).2 n (by simpa using hf)]

/-- Slow-path output for the single-base case agrees with the fast path, when the MRO of
the base starts with the base and has no duplicates: `Objects/typeobject.c:3493-3513` is
purely an optimisation of `pmerge` under the invariants of a C3-computed MRO. -/
theorem fast_slow_agree (self b : α) (baseMro : α → Option (List α)) (m : List α)
    (hm : baseMro b = some (b :: m)) (hnd : (b :: m).Nodup) :
    c3Merge self baseMro [b] = .ok (self :: b :: m) := by
  have hb : b ∉ m := (List.nodup_cons.mp hnd).1
  have hgood : goodHead [b :: m, [b]] b = true := by
    simp [goodHead, tailContains, hb]
  have hadv : advance b [b :: m, [b]] = [m, []] := by simp [advance, advance1]
  have hp : ∀ fuel, m.length + 1 < fuel → pmerge fuel [b :: m, [b]] = .ok (b :: m) := by
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ n =>
      simp only [pmerge, candidateOf, hgood, ite_true, hadv]
      rw [pmerge_single m (List.nodup_cons.mp hnd).2 n (by omega)]
  simp only [c3Merge, firstDuplicate, List.contains_nil, Bool.false_eq_true, ite_false]
  simp only [toMerge, List.map_cons, List.map_nil, hm, Option.getD_some, List.cons_append,
    List.nil_append]
  rw [hp _ (by simp [totalLen])]

/-- **Local precedence, monotonicity (one level)**: the MRO computed by the slow path
extends the MRO of every base and the declared tuple of bases, without reordering. -/
theorem c3Merge_order (self : α) (baseMro : α → Option (List α)) (bases mro : List α)
    (h : c3Merge self baseMro bases = .ok mro) :
    ∃ m, mro = self :: m ∧ bases.Sublist m ∧
      ∀ b ∈ bases, ((baseMro b).getD []).Sublist m := by
  simp only [c3Merge] at h
  cases hd : firstDuplicate bases with
  | some d => rw [hd] at h; simp at h
  | none =>
    rw [hd] at h
    simp only at h
    cases hp : pmerge (totalLen (toMerge baseMro bases) + 1) (toMerge baseMro bases) with
    | ok m =>
      rw [hp] at h
      simp only [Lin.ok.injEq] at h
      refine ⟨m, h.symm, ?_, ?_⟩
      · exact pmerge_sublist _ _ _ hp _ (by simp [toMerge])
      · intro b hb
        apply pmerge_sublist _ _ _ hp
        simp only [toMerge, List.mem_append, List.mem_map]
        exact Or.inl ⟨b, hb, rfl⟩
    | conflict r => rw [hp] at h; simp at h
    | fuel => rw [hp] at h; simp at h

end PyLean.TypeObj
