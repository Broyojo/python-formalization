import PyLean.CoreLibs.Functools.DispatchProps
import PyLean.CoreLibs.Functools.CompareProps

/-!
Statements that a wrong function would fail. Each says what the result is, not what it is not: `_unwrap_partial` follows
`.func` and leaves anything else, `_c3_merge` picks the first head in no tail and raises when there is none, and so on.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-! ### `_unwrap_partial` -/

/-- `_unwrap_partial` goes from a partial to its `func`, and returns anything else as it is. Together the two say what
the result is on every object, which `fun _ => .notCallable` does not meet. -/
def UnwrapPartialChain : Prop :=
  ∀ (α : Type) (g : Fn α) (o : Option Nat) (d : Option (List (String × α))) (a : List (PArg α))
    (k : List (String × α)) (p : Nat) (s : α) (i : Nat) (e : PyExc),
    unwrapPartial (.pobj o d g a k p) = unwrapPartial g ∧ unwrapPartial (.base i : Fn α) = .base i ∧
    unwrapPartial (.notCallable : Fn α) = .notCallable ∧ unwrapPartial (.fails e : Fn α) = .fails e ∧
    unwrapPartial (.bound g s) = .bound g s

theorem unwrapPartialChain_proven : UnwrapPartialChain := by
  intro α g o d a k p s i e
  simp [unwrapPartial]

/-- `_unwrap_partial` on objects by identity, with `next x` the `func` of a partial `x`: `__setstate__` can give a partial
itself as `func`, which the inductive `Fn` cannot hold. `.modelFuel` is the loop not ending. -/
def unwrapLoop (next : Nat → Option Nat) : Nat → Nat → Py Nat
  | 0, _ => .error .modelFuel
  | f + 1, x =>
    match next x with
    | some y => unwrapLoop next f y
    | none => .ok x

/-- The loop ends at an object that is not a partial, on any chain without a cycle. `_unwrap_partial` always ends. False:
`p.__setstate__((p, (), {}, None))` is accepted, and on that `p` the `while` of Lib/functools.py:501 never stops. -/
def UnwrapAlwaysEnds : Prop :=
  ∀ (next : Nat → Option Nat) (x : Nat), ∃ fuel r, unwrapLoop next fuel x = .ok r

theorem unwrapLoop_cycle (next : Nat → Option Nat) (x : Nat) (h : next x = some x) :
    ∀ fuel, unwrapLoop next fuel x = .error .modelFuel := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih => simp [unwrapLoop, h, ih]

theorem unwrapAlwaysEnds_refuted : ¬UnwrapAlwaysEnds := by
  intro h
  obtain ⟨fuel, r, hr⟩ := h (fun _ => some 0) 0
  rw [unwrapLoop_cycle (fun _ => some 0) 0 rfl] at hr
  cases hr

/-- Where the loop ends, it ends at the first object on the chain that is not a partial: every step follows `next`. -/
def UnwrapLoopResult : Prop :=
  ∀ (next : Nat → Option Nat) (fuel x r : Nat), unwrapLoop next fuel x = .ok r →
    next r = none ∧ (next x = none → r = x) ∧ ∀ y, next x = some y → ∃ f, unwrapLoop next f y = .ok r

theorem unwrapLoopResult_proven : UnwrapLoopResult := by
  intro next fuel x r h
  induction fuel generalizing x with
  | zero => simp [unwrapLoop] at h
  | succ n ih =>
    simp only [unwrapLoop] at h
    cases hn : next x with
    | none =>
      simp only [hn, Except.ok.injEq] at h
      subst h
      exact ⟨hn, fun _ => rfl, by simp⟩
    | some y =>
      simp only [hn] at h
      refine ⟨(ih y h).1, by simp, ?_⟩
      intro z hz
      simp only [Option.some.injEq] at hz
      subst hz
      exact ⟨n, h⟩

/-! ### `_unwrap_partialmethod` -/

/-- What `_unwrap_partialmethod` ends at: through every partial, partialmethod and `__partialmethod__` attribute that is
a partialmethod, to the first object that is none of them. -/
def uFinal : UObj → Py UObj
  | .leaf i => .ok (.leaf i)
  | .bad m => .error (.valueError m)
  | .part f => uFinal f
  | .pm f => uFinal f
  | .method a =>
    match a with
    | .pm g => uFinal g
    | _ => .ok (.method a)

private theorem pms_final : ∀ (n : Nat) (f : UObj), uFinal (stripPms n f).1 = uFinal f
  | 0, _ => rfl
  | n + 1, f => by
    cases f with
    | pm g => simp only [stripPms, uFinal]; exact pms_final n g
    | _ => rfl

private theorem parts_final : ∀ (n : Nat) (f : UObj), uFinal (stripParts n f).1 = uFinal f
  | 0, _ => rfl
  | n + 1, f => by
    cases f with
    | part g => simp only [stripParts, uFinal]; exact parts_final n g
    | _ => rfl

private theorem pms_same : ∀ (n : Nat) (f : UObj), (stripPms n f).2 = false → (stripPms n f).1 = f
  | 0, _, _ => rfl
  | n + 1, f, h => by
    cases f <;> simp_all [stripPms]

private theorem parts_same : ∀ (n : Nat) (f : UObj), (stripParts n f).2 = false → (stripParts n f).1 = f
  | 0, _, _ => rfl
  | n + 1, f, h => by
    cases f <;> simp_all [stripParts]

private theorem pms_size : ∀ (n : Nat) (f : UObj), (stripPms n f).1.size ≤ f.size
  | 0, _ => Nat.le_refl _
  | n + 1, f => by
    cases f with
    | pm g =>
      have := pms_size n g
      simp only [stripPms, UObj.size]
      omega
    | _ => simp [stripPms]

private theorem parts_size : ∀ (n : Nat) (f : UObj), (stripParts n f).1.size ≤ f.size
  | 0, _ => Nat.le_refl _
  | n + 1, f => by
    cases f with
    | part g =>
      have := parts_size n g
      simp only [stripParts, UObj.size]
      omega
    | _ => simp [stripParts]

private theorem pms_size_lt : ∀ (n : Nat) (f : UObj), (stripPms n f).2 = true → (stripPms n f).1.size < f.size
  | 0, _, h => by simp [stripPms] at h
  | n + 1, f, h => by
    cases f with
    | pm g =>
      have := pms_size n g
      simp only [stripPms, UObj.size]
      omega
    | _ => simp [stripPms] at h

private theorem parts_size_lt : ∀ (n : Nat) (f : UObj), (stripParts n f).2 = true → (stripParts n f).1.size < f.size
  | 0, _, h => by simp [stripParts] at h
  | n + 1, f, h => by
    cases f with
    | part g =>
      have := parts_size n g
      simp only [stripParts, UObj.size]
      omega
    | _ => simp [stripParts] at h

private theorem step_eq (n : Nat) (f f1 : UObj) (b : Bool) (h : stripMethods (f.size + 1) f = .ok (f1, b)) :
    unwrapPartialmethod (n + 1) f =
      (if b || (stripPms (f1.size + 1) f1).2 ||
            (stripParts ((stripPms (f1.size + 1) f1).1.size + 1) (stripPms (f1.size + 1) f1).1).2 then
        unwrapPartialmethod n (stripParts ((stripPms (f1.size + 1) f1).1.size + 1) (stripPms (f1.size + 1) f1).1).1
       else .ok (stripParts ((stripPms (f1.size + 1) f1).1.size + 1) (stripPms (f1.size + 1) f1).1).1) := by
  simp only [unwrapPartialmethod, h]

/-- `_unwrap_partialmethod` is `uFinal`, for every object: it reaches the same result as following each layer in turn,
and a read of `__partialmethod__` that raises propagates, however deep it is. The result is exact, so a constant fails
this. Fuel is the size of the object: the loop ends on every value of `UObj`, which has no cycles. -/
def UnwrapPartialmethodExact : Prop :=
  ∀ (fuel : Nat) (f : UObj), f.size + 1 ≤ fuel → unwrapPartialmethod fuel f = uFinal f

theorem unwrapPartialmethodExact_proven : UnwrapPartialmethodExact := by
  intro fuel
  induction fuel with
  | zero => intro f h; omega
  | succ n ih =>
    intro f hs
    cases f with
    | leaf i => rw [step_eq n _ (.leaf i) false rfl]; rfl
    | bad m => simp [unwrapPartialmethod, stripMethods, uFinal]
    | part g =>
      rw [step_eq n _ (.part g) false rfl]
      have h1 : stripPms ((UObj.part g).size + 1) (.part g) = (.part g, false) := rfl
      have h2 : stripParts ((UObj.part g).size + 1) (.part g) = ((stripParts (g.size + 1) g).1, true) := rfl
      simp only [h1, h2, Bool.false_or, Bool.or_true, ↓reduceIte]
      have hsz := parts_size (g.size + 1) g
      simp only [UObj.size] at hs
      rw [ih _ (by omega), parts_final]
      rfl
    | pm g =>
      rw [step_eq n _ (.pm g) false rfl]
      have h1 : stripPms ((UObj.pm g).size + 1) (.pm g) = ((stripPms (g.size + 1) g).1, true) := rfl
      simp only [h1, Bool.false_or, Bool.true_or, ↓reduceIte]
      have s1 := pms_size (g.size + 1) g
      have s2 := parts_size ((stripPms (g.size + 1) g).1.size + 1) (stripPms (g.size + 1) g).1
      simp only [UObj.size] at hs
      rw [ih _ (by omega), parts_final, pms_final]
      rfl
    | method a =>
      cases a with
      | pm g =>
        rw [step_eq n _ (.pm g) true rfl]
        simp only [Bool.true_or, ↓reduceIte]
        have s1 := pms_size ((UObj.pm g).size + 1) (.pm g)
        have s2 := parts_size ((stripPms ((UObj.pm g).size + 1) (.pm g)).1.size + 1)
          (stripPms ((UObj.pm g).size + 1) (.pm g)).1
        have e1 : (UObj.pm g).size = g.size + 1 := rfl
        have e2 : (UObj.method (.pm g)).size = g.size + 2 := rfl
        rw [ih _ (by omega), parts_final, pms_final]
        rfl
      | leaf i => rw [step_eq n _ (.method (.leaf i)) false rfl]; rfl
      | part g => rw [step_eq n _ (.method (.part g)) false rfl]; rfl
      | method g => rw [step_eq n _ (.method (.method g)) false rfl]; rfl
      | bad m => rw [step_eq n _ (.method (.bad m)) false rfl]; rfl

/-! ### `_c3_merge` -/

/-- Heads as the search sees them, for `seqs` as a whole. -/
private def headTest (all : List (List Cls)) (s : List Cls) : Option Cls :=
  match s with
  | [] => none
  | c :: _ => if all.any (fun t => t.tail.contains c) then none else some c

private theorem find_some (all : List (List Cls)) : ∀ (l : List (List Cls)) (c : Cls),
    l.findSome? (headTest all) = some c → ∃ pre t post, l = pre ++ (c :: t) :: post ∧
      (∀ u ∈ all, c ∉ u.tail) ∧ ∀ p ∈ pre, headTest all p = none
  | [], _, h => by simp at h
  | x :: xs, c, h => by
    simp only [List.findSome?_cons] at h
    cases hx : headTest all x with
    | none =>
      simp only [hx] at h
      obtain ⟨pre, t, post, h1, h2, h3⟩ := find_some all xs c h
      refine ⟨x :: pre, t, post, by simp [h1], h2, ?_⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hx
      · exact h3 p hp
    | some y =>
      simp only [hx, Option.some.injEq] at h
      subst h
      cases x with
      | nil => simp [headTest] at hx
      | cons z t =>
        simp only [headTest] at hx
        split at hx
        · simp at hx
        · rename_i hn
          simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨[], t, xs, rfl, ?_, by simp⟩
          intro u hu hin
          apply hn
          exact List.any_eq_true.2 ⟨u, hu, by simpa using hin⟩

private theorem find_none (all : List (List Cls)) : ∀ (l : List (List Cls)),
    l.findSome? (headTest all) = none → ∀ s ∈ l, ∀ c t, s = c :: t → ∃ u ∈ all, c ∈ u.tail
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.findSome?_cons] at h
    intro s hs c t he
    cases hx : headTest all x with
    | some y => simp [hx] at h
    | none =>
      simp only [hx] at h
      rcases List.mem_cons.1 hs with rfl | hs
      · subst he
        simp only [headTest] at hx
        split at hx
        · rename_i ha
          obtain ⟨u, hu, hin⟩ := List.any_eq_true.1 ha
          exact ⟨u, hu, by simpa using hin⟩
        · simp at hx
      · exact find_none all xs h s hs c t he

/-- `_c3_merge` chooses by the rule of C3. The candidate is the head of the first sequence that is not in the tail of any
sequence, every earlier sequence's head being rejected, and with no such head the merge is a `RuntimeError`. A merge that
always takes the first head fails this. -/
def C3CandidateRule : Prop :=
  ∀ (seqs : List (List Cls)) (c : Cls) (fuel : Nat),
    (candidateOf seqs = some c → ∃ pre t post, seqs = pre ++ (c :: t) :: post ∧ (∀ u ∈ seqs, c ∉ u.tail) ∧
      ∀ p ∈ pre, ∀ h r, p = h :: r → ∃ u ∈ seqs, h ∈ u.tail) ∧
    (candidateOf seqs = none → ∀ s ∈ seqs, ∀ h r, s = h :: r → ∃ u ∈ seqs, h ∈ u.tail) ∧
    ((∀ s ∈ seqs, s ≠ []) → seqs ≠ [] → candidateOf seqs = none →
      c3Merge (fuel + 1) seqs = .error (.named "RuntimeError" "Inconsistent hierarchy"))

private theorem cand_eq (seqs : List (List Cls)) : candidateOf seqs = seqs.findSome? (headTest seqs) := by
  rfl

private theorem filter_self {seqs : List (List Cls)} (h : ∀ s ∈ seqs, s ≠ []) :
    seqs.filter (fun s => !s.isEmpty) = seqs := by
  apply List.filter_eq_self.2
  intro s hs
  cases s with
  | nil => exact absurd rfl (h _ hs)
  | cons _ _ => rfl

theorem c3CandidateRule_proven : C3CandidateRule := by
  intro seqs c fuel
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [cand_eq] at h
    obtain ⟨pre, t, post, h1, h2, h3⟩ := find_some seqs seqs c h
    refine ⟨pre, t, post, h1, h2, ?_⟩
    intro p hp x r he
    have := h3 p hp
    subst he
    simp only [headTest] at this
    split at this
    · rename_i ha
      obtain ⟨u, hu, hin⟩ := List.any_eq_true.1 ha
      exact ⟨u, hu, by simpa using hin⟩
    · simp at this
  · intro h s hs x r he
    rw [cand_eq] at h
    exact find_none seqs seqs h s hs x r he
  · intro h1 h2 h3
    have hne : (seqs.isEmpty) = false := by cases seqs <;> simp_all
    simp only [c3Merge, filter_self h1, hne, Bool.false_eq_true, ↓reduceIte, h3]

private theorem merge_step {fuel : Nat} {seqs : List (List Cls)} {r : List Cls} (h : c3Merge (fuel + 1) seqs = .ok r) :
    let s := seqs.filter (fun s => !s.isEmpty)
    (s = [] ∧ r = []) ∨ ∃ c rest, candidateOf s = some c ∧ r = c :: rest ∧
      c3Merge fuel (s.map (fun x => if x.head? = some c then x.tail else x)) = .ok rest := by
  intro s
  simp only [c3Merge] at h
  split at h
  · rename_i he
    left
    simp only [Except.ok.injEq] at h
    exact ⟨by simpa [s] using he, h.symm⟩
  · split at h
    · simp at h
    · rename_i c hc
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inr ⟨c, rest, hc, h.symm, hrest⟩

private theorem cand_props {s : List (List Cls)} {c : Cls} (h : candidateOf s = some c) :
    (∀ u ∈ s, c ∉ u.tail) ∧ ∃ t, (c :: t) ∈ s := by
  rw [cand_eq] at h
  obtain ⟨pre, t, post, h1, h2, _⟩ := find_some s s c h
  exact ⟨h2, t, by simp [h1]⟩

/-- `_c3_merge` loses and adds nothing: on sequences without repeats the result has no repeats, and it holds exactly the
elements of the sequences. With `C3CandidateRule` and `C3MergeMonotone` this is the whole of C3. -/
def C3MergeElems : Prop :=
  ∀ (fuel : Nat) (seqs : List (List Cls)) (r : List Cls), c3Merge fuel seqs = .ok r → (∀ s ∈ seqs, s.Nodup) →
    r.Nodup ∧ ∀ x, x ∈ r ↔ ∃ s ∈ seqs, x ∈ s

theorem c3MergeElems_proven : C3MergeElems := by
  intro fuel
  induction fuel with
  | zero => intro seqs r h; simp [c3Merge] at h
  | succ n ih =>
    intro seqs r h hn
    rcases merge_step h with ⟨h1, h2⟩ | ⟨c, rest, h1, h2, h3⟩
    · subst h2
      refine ⟨by simp, fun x => ?_⟩
      simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro s hs hx
      have : s ∈ seqs.filter (fun s => !s.isEmpty) := List.mem_filter.2 ⟨hs, by cases s <;> simp_all⟩
      rw [h1] at this
      simp at this
    · subst h2
      obtain ⟨hc, t, ht⟩ := cand_props h1
      have hfm : ∀ x, x ∈ seqs.filter (fun s => !s.isEmpty) → x ∈ seqs := fun x hx => (List.mem_filter.1 hx).1
      have hn' : ∀ x ∈ (seqs.filter (fun s => !s.isEmpty)).map (fun x => if x.head? = some c then x.tail else x),
          x.Nodup := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have hyn := hn y (hfm y hy)
        split
        · exact (List.Nodup.sublist (List.tail_sublist y) hyn)
        · exact hyn
      obtain ⟨h4, h5⟩ := ih _ _ h3 hn'
      have hgone : c ∉ rest := by
        intro hin
        obtain ⟨x, hx, hcx⟩ := (h5 c).1 hin
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have hty := hc y hy
        cases y with
        | nil => simp at hcx
        | cons a b =>
          by_cases he : a = c
          · subst he
            simp only [List.head?_cons, ↓reduceIte, List.tail_cons] at hcx
            exact hty hcx
          · have : (a :: b).head? ≠ some c := by simpa using he
            simp only [this, ↓reduceIte] at hcx
            rcases List.mem_cons.1 hcx with h6 | h6
            · exact he h6.symm
            · exact hty h6
      refine ⟨List.nodup_cons.2 ⟨hgone, h4⟩, ?_⟩
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨_, hfm _ ht, by simp⟩
        · obtain ⟨y, hy, hxy⟩ := (h5 x).1 hx
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          refine ⟨z, hfm z hz, ?_⟩
          split at hxy
          · exact List.mem_of_mem_tail hxy
          · exact hxy
      · rintro ⟨y, hy, hxy⟩
        by_cases hxc : x = c
        · subst hxc; simp
        · refine List.mem_cons_of_mem _ ((h5 x).2 ?_)
          have hyf : y ∈ seqs.filter (fun s => !s.isEmpty) := List.mem_filter.2 ⟨hy, by cases y <;> simp_all⟩
          refine ⟨_, List.mem_map.2 ⟨y, hyf, rfl⟩, ?_⟩
          split
          · rename_i he
            cases y with
            | nil => simp at hxy
            | cons a b =>
              simp only [List.head?_cons, Option.some.injEq] at he
              simp only [List.tail_cons]
              rcases List.mem_cons.1 hxy with h7 | h7
              · exact absurd (h7.trans he) hxc
              · exact h7
          · exact hxy

private theorem sum_lt {β : Type} (f : β → β) (g : β → Nat) : ∀ (l : List β) (x : β), x ∈ l → g (f x) < g x →
    (∀ y ∈ l, g (f y) ≤ g y) → ((l.map f).map g).sum < (l.map g).sum
  | [], _, h, _, _ => by simp at h
  | a :: r, x, hx, hlt, hle => by
    simp only [List.map_cons, List.sum_cons]
    have ha := hle a (by simp)
    have hsum : ((r.map f).map g).sum ≤ (r.map g).sum := by
      have aux : ∀ l : List β, (∀ y ∈ l, g (f y) ≤ g y) → ((l.map f).map g).sum ≤ (l.map g).sum := by
        intro l
        induction l with
        | nil => simp
        | cons b t ih =>
          intro h
          simp only [List.map_cons, List.sum_cons]
          have := h b (by simp)
          have := ih (fun y hy => h y (by simp [hy]))
          omega
      exact aux r (fun y hy => hle y (by simp [hy]))
    rcases List.mem_cons.1 hx with rfl | hx'
    · omega
    · have := sum_lt f g r x hx' hlt (fun y hy => hle y (by simp [hy]))
      omega

private theorem sum_filter_le (seqs : List (List Cls)) :
    ((seqs.filter (fun s => !s.isEmpty)).map List.length).sum ≤ (seqs.map List.length).sum := by
  induction seqs with
  | nil => simp
  | cons s r ih =>
    cases s with
    | nil => simpa using ih
    | cons a b => simp [ih]

/-- `_c3_merge` always ends: each pass removes an element, so a fuel of the total length is enough for `_c3_mro`, and the
loop has no case that does not finish. -/
def C3MergeEnds : Prop :=
  ∀ (fuel : Nat) (seqs : List (List Cls)), (seqs.map List.length).sum < fuel → c3Merge fuel seqs ≠ .error .modelFuel

theorem c3MergeEnds_proven : C3MergeEnds := by
  intro fuel
  induction fuel with
  | zero => intro seqs h; omega
  | succ n ih =>
    intro seqs h
    simp only [c3Merge]
    split
    · simp
    · split
      · simp
      · rename_i c hc
        obtain ⟨_, t, ht⟩ := cand_props hc
        have hlt := sum_lt (fun x => if x.head? = some c then x.tail else x) List.length
          (seqs.filter (fun s => !s.isEmpty)) (c :: t) ht (by simp) (by
            intro y _
            split
            · simp
            · exact Nat.le_refl _)
        have hf := sum_filter_le seqs
        have := ih ((seqs.filter (fun s => !s.isEmpty)).map (fun x => if x.head? = some c then x.tail else x))
          (by omega)
        simp only [bind, Except.bind]
        split
        · rename_i e he
          rw [he] at this
          simpa using this
        · simp [pure, Except.pure]

private theorem merge_sub : ∀ (fuel : Nat) (seqs : List (List Cls)) (r : List Cls), c3Merge fuel seqs = .ok r →
    ∀ x ∈ r, ∃ s ∈ seqs, x ∈ s := by
  intro fuel
  induction fuel with
  | zero => intro seqs r h; simp [c3Merge] at h
  | succ n ih =>
    intro seqs r h x hx
    rcases merge_step h with ⟨_, h2⟩ | ⟨c, rest, h1, h2, h3⟩
    · subst h2
      simp at hx
    · subst h2
      have hfm : ∀ y, y ∈ seqs.filter (fun s => !s.isEmpty) → y ∈ seqs := fun y hy => (List.mem_filter.1 hy).1
      rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨_, t, ht⟩ := cand_props h1
        exact ⟨_, hfm _ ht, by simp⟩
      · obtain ⟨y, hy, hxy⟩ := ih _ _ h3 x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        refine ⟨z, hfm z hz, ?_⟩
        split at hxy
        · exact List.mem_of_mem_tail hxy
        · exact hxy

/-! ### `_c3_mro` -/

/-- The laws of `issubclass` on a real hierarchy: reflexive, true of a class and a base, and transitive. A class with a
`__subclasshook__` can break them, and then the hypotheses say which classes the statement is about. -/
structure SubLaws (W : World) : Prop where
  refl : ∀ c, W.isSub c c = .ok true
  base : ∀ c b, b ∈ W.bases c → W.isSub c b = .ok true
  trans : ∀ a b c, W.isSub a b = .ok true → W.isSub b c = .ok true → W.isSub a c = .ok true

theorem mapPy_mem {α β : Type} (f : α → Py β) : ∀ (l : List α) (rs : List β), mapPy f l = .ok rs →
    ∀ r ∈ rs, ∃ b ∈ l, f b = .ok r
  | [], rs, h, r, hr => by
    simp only [mapPy, Except.ok.injEq] at h
    subst h
    simp at hr
  | x :: xs, rs, h, r, hr => by
    simp only [mapPy, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i y hy
      split at h
      · simp at h
      · rename_i ys hys
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨x, by simp, hy⟩
        · obtain ⟨b, hb, hf⟩ := mapPy_mem f xs ys hys r hr
          exact ⟨b, by simp [hb], hf⟩

private theorem introduces_sub {W : World} {cls b : Cls} (h : introduces W cls b = .ok true) :
    W.isSub cls b = .ok true := by
  simp only [introduces] at h
  split at h
  · simp at h
  · simp at h
  · assumption

private theorem c3Mro_parts {W : World} {fuel : Nat} {cls : Cls} {abcs r : List Cls}
    (h : c3Mro W (fuel + 1) cls abcs = .ok r) :
    ∃ ab e a o, filterPy (introduces W cls) abcs = .ok ab ∧
      mapPy (fun b => c3Mro W fuel b (ab.foldl List.erase abcs)) ((W.bases cls).take (boundaryOf W (W.bases cls))) = .ok e ∧
      mapPy (fun b => c3Mro W fuel b (ab.foldl List.erase abcs)) ab = .ok a ∧
      mapPy (fun b => c3Mro W fuel b (ab.foldl List.erase abcs)) ((W.bases cls).drop (boundaryOf W (W.bases cls))) = .ok o ∧
      ∃ n, c3Merge n ([[cls]] ++ e ++ a ++ o ++ [(W.bases cls).take (boundaryOf W (W.bases cls))] ++ [ab] ++
        [(W.bases cls).drop (boundaryOf W (W.bases cls))]) = .ok r := by
  simp only [c3Mro, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i ab hab
  split at h
  · simp at h
  rename_i e he
  split at h
  · simp at h
  rename_i a ha
  split at h
  · simp at h
  rename_i o ho
  exact ⟨ab, e, a, o, hab, he, ha, ho, _, h⟩

/-- Everything `_c3_mro` returns is something `cls` is a subclass of, so "Unrelated ABCs are ignored and don't end up in the
result": an ABC for which `issubclass(cls, abc)` is false cannot be in it. Any list with an extra class fails this. -/
def C3MroRelated : Prop :=
  ∀ (W : World), SubLaws W → ∀ (fuel : Nat) (cls : Cls) (abcs r : List Cls), c3Mro W fuel cls abcs = .ok r →
    ∀ x ∈ r, W.isSub cls x = .ok true

theorem c3MroRelated_proven : C3MroRelated := by
  intro W L fuel
  induction fuel with
  | zero => intro cls abcs r h; simp [c3Mro] at h
  | succ n ih =>
    intro cls abcs r h x hx
    obtain ⟨ab, e, a, o, h1, h2, h3, h4, m, h5⟩ := c3Mro_parts h
    obtain ⟨s, hs, hxs⟩ := merge_sub m _ r h5 x hx
    have hb : ∀ b ∈ W.bases cls, W.isSub cls b = .ok true := L.base cls
    have hmid : ∀ b ∈ ab, W.isSub cls b = .ok true := fun b hb' =>
      introduces_sub (filterPy_sat _ _ _ b h1 hb').2
    have rec_ : ∀ (l : List Cls) (rs : List (List Cls)), (∀ b ∈ l, W.isSub cls b = .ok true) →
        mapPy (fun b => c3Mro W n b (ab.foldl List.erase abcs)) l = .ok rs → s ∈ rs → W.isSub cls x = .ok true := by
      intro l rs hl hm hrs
      obtain ⟨b, hbl, hf⟩ := mapPy_mem _ _ _ hm s hrs
      exact L.trans _ _ _ (hl b hbl) (ih b _ _ hf x hxs)
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with ((((((hs | hs) | hs) | hs) | hs) | hs) | hs)
    · subst hs
      simp only [List.mem_singleton] at hxs
      subst hxs
      exact L.refl _
    · exact rec_ _ _ (fun b hb' => hb b (List.mem_of_mem_take hb')) h2 hs
    · exact rec_ _ _ hmid h3 hs
    · exact rec_ _ _ (fun b hb' => hb b (List.mem_of_mem_drop hb')) h4 hs
    · subst hs
      exact hb x (List.mem_of_mem_take hxs)
    · subst hs
      exact hmid x hxs
    · subst hs
      exact hb x (List.mem_of_mem_drop hxs)

private theorem filterPy_sublist {α : Type} (p : α → Py Bool) : ∀ (l r : List α), filterPy p l = .ok r → r.Sublist l
  | [], r, h => by
    simp only [filterPy, Except.ok.injEq] at h
    subst h
    exact List.Sublist.refl _
  | x :: xs, r, h => by
    simp only [filterPy] at h
    split at h
    · simp at h
    · rename_i b _
      split at h
      · simp at h
      · rename_i t ht
        simp only [Except.ok.injEq] at h
        subst h
        have := filterPy_sublist p xs t ht
        cases b with
        | true => exact List.Sublist.cons₂ _ this
        | false => exact List.Sublist.cons _ this

private theorem foldl_erase_nodup (ab : List Cls) : ∀ abcs : List Cls, abcs.Nodup → (ab.foldl List.erase abcs).Nodup := by
  induction ab with
  | nil => intro _ h; exact h
  | cons x xs ih =>
    intro abcs h
    exact ih _ (h.erase x)

/-- On a class whose `__bases__` has no repeats, and a list of ABCs without repeats, `_c3_mro` has no repeats. -/
def C3MroNoRepeat : Prop :=
  ∀ (W : World), (∀ c, (W.bases c).Nodup) → ∀ (fuel : Nat) (cls : Cls) (abcs r : List Cls), abcs.Nodup →
    c3Mro W fuel cls abcs = .ok r → r.Nodup

theorem c3MroNoRepeat_proven : C3MroNoRepeat := by
  intro W hb fuel
  induction fuel with
  | zero => intro cls abcs r _ h; simp [c3Mro] at h
  | succ n ih =>
    intro cls abcs r ha h
    obtain ⟨ab, e, a, o, h1, h2, h3, h4, m, h5⟩ := c3Mro_parts h
    have hab : ab.Nodup := (filterPy_sublist _ _ _ h1).nodup ha
    have ha' := foldl_erase_nodup ab abcs ha
    have rec_ : ∀ (l : List Cls) (rs : List (List Cls)),
        mapPy (fun b => c3Mro W n b (ab.foldl List.erase abcs)) l = .ok rs → ∀ s ∈ rs, s.Nodup := by
      intro l rs hm s hs
      obtain ⟨b, _, hf⟩ := mapPy_mem _ _ _ hm s hs
      exact ih b _ _ ha' hf
    refine (c3MergeElems_proven m _ r h5 ?_).1
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with ((((((hs | hs) | hs) | hs) | hs) | hs) | hs)
    · subst hs; simp
    · exact rec_ _ _ h2 s hs
    · exact rec_ _ _ h3 s hs
    · exact rec_ _ _ h4 s hs
    · subst hs; exact (List.take_sublist _ _).nodup (hb cls)
    · subst hs; exact hab
    · subst hs; exact (List.drop_sublist _ _).nodup (hb cls)

/-- The ABCs that `_c3_mro` inserts at this class are exactly those of `abcs` that `cls` is a subclass of and no direct
base is: the docstring's "where their functionality is introduced". `issubclass` raising is the error of the call. -/
def C3MroIntroduced : Prop :=
  ∀ (W : World) (cls : Cls) (abcs ab : List Cls), filterPy (introduces W cls) abcs = .ok ab →
    ∀ x, x ∈ ab ↔ x ∈ abcs ∧ W.isSub cls x = .ok true ∧ anyPy (fun b => W.isSub b x) (W.bases cls) = .ok false

theorem c3MroIntroduced_proven : C3MroIntroduced := by
  intro W cls abcs ab h x
  constructor
  · intro hx
    obtain ⟨h1, h2⟩ := filterPy_sat _ _ _ x h hx
    refine ⟨h1, introduces_sub h2, ?_⟩
    simp only [introduces] at h2
    split at h2
    · simp at h2
    · simp at h2
    · split at h2
      · simp at h2
      · rename_i b hb
        cases b with
        | true => simp at h2
        | false => exact hb
  · rintro ⟨h1, h2, h3⟩
    refine filterPy_mem _ _ _ x h h1 ?_
    simp only [introduces, h2, h3, Bool.not_false]

private theorem find_zip (p : Cls → Bool) : ∀ (r : List Cls) (n : Nat),
    (r.zipIdx (n + 1)).find? (fun q => p q.1) = ((r.zipIdx n).find? (fun q => p q.1)).map (fun q => (q.1, q.2 + 1))
  | [], _ => rfl
  | x :: t, n => by
    simp only [List.zipIdx_cons, List.find?_cons]
    cases p x with
    | true => rfl
    | false => exact find_zip p t (n + 1)

private theorem boundary_snoc (W : World) (l : List Cls) (x : Cls) :
    boundaryOf W (l ++ [x]) = if W.isAbc x then l.length + 1 else boundaryOf W l := by
  simp only [boundaryOf, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.zipIdx_cons, List.find?_cons, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  cases hx : W.isAbc x with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [find_zip]
    cases hf : (l.reverse.zipIdx 0).find? (fun q => W.isAbc q.1) with
    | none => rfl
    | some q => simp

/-- The boundary of `_c3_mro` is the place after the last base with `__abstractmethods__`: no base after it has them, and
the one just before it does. So a wrong boundary fails this. -/
def BoundaryExact : Prop :=
  ∀ (W : World) (bases : List Cls), boundaryOf W bases ≤ bases.length ∧
    (∀ b ∈ bases.drop (boundaryOf W bases), W.isAbc b = false) ∧
    ∀ j, boundaryOf W bases = j + 1 → ∃ b, bases[j]? = some b ∧ W.isAbc b = true

theorem boundaryExact_proven : BoundaryExact := by
  intro W bases
  have key : ∀ r : List Cls, boundaryOf W r.reverse ≤ r.reverse.length ∧
      (∀ b ∈ r.reverse.drop (boundaryOf W r.reverse), W.isAbc b = false) ∧
      ∀ j, boundaryOf W r.reverse = j + 1 → ∃ b, r.reverse[j]? = some b ∧ W.isAbc b = true := by
    intro r
    induction r with
    | nil => simp [boundaryOf]
    | cons x t ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [List.reverse_cons, boundary_snoc, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      cases hx : W.isAbc x with
      | true =>
        simp only [↓reduceIte]
        refine ⟨Nat.le_refl _, ?_, ?_⟩
        · intro b hb
          rw [List.drop_of_length_le (by simp)] at hb
          simp at hb
        · intro j hj
          have : j = t.reverse.length := by omega
          subst this
          exact ⟨x, by simp, hx⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, ?_, ?_⟩
        · intro b hb
          rw [List.drop_append_of_le_length h1] at hb
          rcases List.mem_append.1 hb with hb | hb
          · exact h2 b hb
          · simp only [List.mem_singleton] at hb
            subst hb
            exact hx
        · intro j hj
          obtain ⟨b, hb, hc⟩ := h3 j hj
          have hlt : j < t.reverse.length := by omega
          exact ⟨b, by rw [List.getElem?_append_left hlt]; exact hb, hc⟩
  have := key bases.reverse
  simpa using this

/-! ### `_compose_mro` -/

/-- A subclass has the class in its `__mro__`, as `type.__subclasses__` promises. -/
def SubclassLaw (W : World) : Prop := ∀ t sub, sub ∈ W.subclasses t → t ∈ W.mro sub

private def stepFold (acc : List Cls) (ss : List (List Cls)) : List Cls :=
  ss.foldl (fun acc sub => sub.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) acc) acc

private theorem inner_mem (y : Cls) : ∀ (l a : List Cls),
    y ∈ l.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) a ↔ y ∈ a ∨ y ∈ l
  | [], a => by simp
  | u :: us, a => by
    simp only [List.foldl_cons]
    rw [inner_mem y us]
    by_cases hu : u ∈ a
    · simp only [hu, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl h
        · subst h; exact .inl hu
        · exact .inr h
    · simp only [hu, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h

private theorem outer_mem (y : Cls) : ∀ (ss : List (List Cls)) (a : List Cls),
    y ∈ stepFold a ss ↔ y ∈ a ∨ ∃ s ∈ ss, y ∈ s
  | [], a => by simp [stepFold]
  | s :: r, a => by
    simp only [stepFold, List.foldl_cons]
    have := outer_mem y r (s.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) a)
    simp only [stepFold] at this
    rw [this, inner_mem]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

private theorem step_elems (W : World) (L : SubclassLaw W) (cls : Cls) (T : List Cls) (acc r : List Cls) (typ : Cls)
    (ht : typ ∈ T) (h : composeStep W cls T acc typ = .ok r) :
    typ ∈ r ∧ (∀ x ∈ acc, x ∈ r) ∧ ∀ x ∈ r, x ∈ acc ∨ x ∈ T := by
  simp only [composeStep, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i found hf
  simp only [pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨by simp, fun x hx => by simp [hx], ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact .inr ht
  · rename_i hne
    simp only [Except.ok.injEq] at h
    subst h
    have hsorted : ∀ y, (y ∈ found.mergeSort (fun a b => a.length ≥ b.length)) ↔ y ∈ found :=
      fun y => (List.mergeSort_perm _ _).mem_iff
    have hfound : ∀ s ∈ found, ∀ x ∈ s, x ∈ T := by
      simp only [foundFor, bind, Except.bind] at hf
      split at hf
      · simp at hf
      · simp only [pure, Except.pure, Except.ok.injEq] at hf
        subst hf
        intro s hs
        obtain ⟨sub, _, rfl⟩ := List.mem_map.1 hs
        intro x hx
        simpa using (List.mem_filter.1 hx).2
    have htyp : ∃ s ∈ found, typ ∈ s := by
      simp only [foundFor, bind, Except.bind] at hf
      split at hf
      · simp at hf
      · rename_i subs hsubs
        simp only [pure, Except.pure, Except.ok.injEq] at hf
        subst hf
        cases subs with
        | nil => simp at hne
        | cons sub r =>
          have hs := (filterPy_sat _ _ _ sub hsubs (by simp)).1
          refine ⟨_, List.mem_map.2 ⟨sub, by simp, rfl⟩, ?_⟩
          exact List.mem_filter.2 ⟨L _ _ hs, by simpa using ht⟩
    have hm : ∀ y, y ∈ stepFold acc (found.mergeSort (fun a b => a.length ≥ b.length)) ↔
        y ∈ acc ∨ ∃ s ∈ found, y ∈ s := by
      intro y
      rw [outer_mem]
      simp only [hsorted]
    refine ⟨(hm typ).2 (.inr htyp), fun x hx => (hm x).2 (.inl hx), ?_⟩
    intro x hx
    rcases (hm x).1 hx with h1 | ⟨s, hs, h1⟩
    · exact .inl h1
    · exact .inr (hfound s hs x h1)

private theorem fold_elems (W : World) (L : SubclassLaw W) (cls : Cls) (T : List Cls) :
    ∀ (l acc r : List Cls), (∀ x ∈ l, x ∈ T) → foldPy (composeStep W cls T) acc l = .ok r →
      ∀ x, x ∈ acc ∨ x ∈ l → x ∈ r
  | [], acc, r, _, h => by
    simp only [foldPy, Except.ok.injEq] at h
    subst h
    intro x hx
    simpa using hx
  | t :: rest, acc, r, hl, h => by
    simp only [foldPy] at h
    split at h
    · simp at h
    rename_i a' hs
    obtain ⟨h1, h2, _⟩ := step_elems W L cls T acc a' t (hl t (by simp)) hs
    have ih := fold_elems W L cls T rest a' r (fun x hx => hl x (by simp [hx])) h
    intro x hx
    rcases hx with hx | hx
    · exact ih x (.inl (h2 x hx))
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ih x (.inl h1)
      · exact ih x (.inr hx)

/-- `_compose_mro` selects exactly: with `T` the related types that are not strict bases of another, the list of ABCs it
passes on holds every one of them, and nothing else, through both branches, the stabilising sort included. -/
def ComposeAbcsExact : Prop :=
  ∀ (W : World), SubclassLaw W → ∀ (cls : Cls) (types sel r : List Cls), filterPy (isRelated W cls) types = .ok sel →
    composeAbcs W cls types = .ok r → ∀ x, x ∈ r ↔ x ∈ sel.filter (fun t => !isStrictBase W sel t)

theorem composeAbcsExact_proven : ComposeAbcsExact := by
  intro W L cls types sel r hs hr x
  simp only [composeAbcs, hs, bind, Except.bind] at hr
  have hmem := fold_elems W L cls (sel.filter (fun t => !isStrictBase W sel t)) _ [] r (fun _ h => h) hr
  have sub : ∀ y, y ∈ r → y ∈ sel.filter (fun t => !isStrictBase W sel t) := by
    have aux : ∀ (l acc r' : List Cls), (∀ y ∈ l, y ∈ sel.filter (fun t => !isStrictBase W sel t)) →
        (∀ y ∈ acc, y ∈ sel.filter (fun t => !isStrictBase W sel t)) →
        foldPy (composeStep W cls (sel.filter (fun t => !isStrictBase W sel t))) acc l = .ok r' →
        ∀ y ∈ r', y ∈ sel.filter (fun t => !isStrictBase W sel t) := by
      intro l
      induction l with
      | nil =>
        intro acc r' _ ha h
        simp only [foldPy, Except.ok.injEq] at h
        subst h
        exact ha
      | cons t rest ih =>
        intro acc r' hl ha h
        simp only [foldPy] at h
        split at h
        · simp at h
        rename_i a' hs'
        obtain ⟨_, _, h2⟩ := step_elems W L cls _ acc a' t (hl t (by simp)) hs'
        refine ih a' r' (fun y hy => hl y (by simp [hy])) ?_ h
        intro y hy
        rcases h2 y hy with h3 | h3
        · exact ha y h3
        · exact h3
    exact aux _ [] r (fun _ h => h) (by simp) hr
  constructor
  · exact sub x
  · intro hx
    exact hmem x (.inr hx)

/-- `_compose_mro` is `_c3_mro` on those ABCs, so all it returns is related to `cls`, and an ABC that the class introduces is
in the result. It never names a class that `cls` is no subclass of. -/
def ComposeMroSpec : Prop :=
  ∀ (W : World), SubLaws W → ∀ (fuel : Nat) (cls : Cls) (types r : List Cls), composeMro W fuel cls types = .ok r →
    ∃ abcs, composeAbcs W cls types = .ok abcs ∧ c3Mro W fuel cls abcs = .ok r ∧ ∀ x ∈ r, W.isSub cls x = .ok true

theorem composeMroSpec_proven : ComposeMroSpec := by
  intro W L fuel cls types r h
  simp only [composeMro, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i abcs ha
  exact ⟨abcs, ha, h, c3MroRelated_proven W L fuel cls abcs r h⟩

/-- The ABCs passed on from `_compose_mro` have no repeats. False: the loop at Lib/functools.py:838-839 appends `typ`
without the test that :845 has, so a type already added through a subclass of an earlier one goes in twice, and
`_c3_merge` then sees it in a tail of its own list and raises `RuntimeError`. -/
def ComposeNoRepeat : Prop :=
  ∀ (W : World) (cls : Cls) (types r : List Cls), composeAbcs W cls types = .ok r → r.Nodup

/-- `cls` is 0, `A` is 1, `B` is 2, `Mid(B)` is 3, `Sub(A, Mid)` is 4, `object` is 5; `Mid` refuses `cls` by its hook. -/
def repeatWorld : World where
  bases := fun c => match c with
    | 0 | 1 | 2 => [5]
    | 3 => [2]
    | 4 => [1, 3]
    | _ => []
  mro := fun c => match c with
    | 0 => [0, 5]
    | 1 => [1, 5]
    | 2 => [2, 5]
    | 3 => [3, 2, 5]
    | 4 => [4, 1, 3, 2, 5]
    | _ => [5]
  isSub := fun a b => .ok (if a == 0 then b != 3 else true)
  isAbc := fun c => c != 0 && c != 5
  subclasses := fun c => match c with
    | 1 => [4]
    | 2 => [3]
    | 3 => [4]
    | _ => []
  isType := fun _ => true
  isAlias := fun _ => false

theorem composeNoRepeat_refuted : ¬ComposeNoRepeat := by
  intro h
  have := h repeatWorld 0 [1, 2] [1, 2, 2] (by decide +kernel)
  revert this
  decide

/-! ### `singledispatch` -/

private theorem lookup_regSet {ι : Type} : ∀ (r : Registry ι) (c : Cls) (f : ι), (regSet r c f).lookup c = some f
  | [], c, f => by simp [regSet]
  | p :: ps, c, f => by
    obtain ⟨a, b⟩ := p
    simp only [regSet]
    by_cases h : a = c
    · subst h; simp
    · have h1 : (a == c) = false := by simpa using h
      have h2 : (c == a) = false := by
        have : c ≠ a := fun e => h e.symm
        simpa using this
      simp only [h1, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, h2]
      exact lookup_regSet ps c f

/-- `singledispatch` from end to end. A new dispatcher calls `func` for `object`; `register` stores under the class, and a
call whose first argument is of that class gets that function, whatever `func` is; a second call is answered from the
cache; no argument is the `TypeError` with `funcname`; and `register` clears the cache. -/
def SingledispatchCalls : Prop :=
  ∀ (ι : Type) (W : World) (fuel tok : Nat) (object c : Cls) (func f : ι) (n : Option String) (d : Dispatcher ι),
    singledispatch object func (.ok n) = .ok d →
    (dispatchCall W fuel tok d (some object)).1 = .ok (some func) ∧
    (dispatchCall W fuel tok d none).1 = .error (.typeError s!"{n.getD "singledispatch function"} requires at least 1 positional argument") ∧
    ∃ d1, register W tok d (.val (.cls c)) (some f) = .ok (.func f, d1) ∧ d1.cache = [] ∧
      (dispatchCall W fuel tok d1 (some c)).1 = .ok (some f) ∧
      (dispatchCall W fuel tok (dispatchCall W fuel tok d1 (some c)).2 (some c)).1 = .ok (some f)

theorem singledispatchCalls_proven : SingledispatchCalls := by
  intro ι W fuel tok object c func f n d h
  simp only [singledispatch, Except.ok.injEq] at h
  subst h
  refine ⟨?_, rfl, regStore W tok ⟨[(object, func)], [], none, n.getD "singledispatch function"⟩ (.cls c) f, rfl, rfl, ?_, ?_⟩
  · simp [dispatchCall, dispatch, tokenSync, dispatchCached]
  · have hl : (regSet [(object, func)] c f).lookup c = some f := lookup_regSet _ _ _
    by_cases ht : W.isAbc c = true <;>
      simp [dispatchCall, dispatch, tokenSync, dispatchCached, regStore, ht, hl]
  · have hl : (regSet [(object, func)] c f).lookup c = some f := lookup_regSet _ _ _
    by_cases ht : W.isAbc c = true <;>
      simp [dispatchCall, dispatch, tokenSync, dispatchCached, regStore, ht, hl]

/-! ### `total_ordering` -/

private theorem addMissing_refused (c : OrdClass) (roots : List OrdOp) (o : OrdOp) (s : Shape) (e : PyExc)
    (hs : c.setAttr o s = .error e) : ∀ (l pre post : List (OrdOp × Shape)),
    l.filter (fun p => decide (p.1 ∉ roots)) = pre ++ (o, s) :: post → (∀ p ∈ pre, c.setAttr p.1 p.2 = .ok ()) →
    addMissing c roots l = .error e := by
  intro l
  induction l with
  | nil => intro pre post h; cases pre <;> simp at h
  | cons x r ih =>
    intro pre post h hp
    obtain ⟨a, b⟩ := x
    by_cases ha : a ∈ roots
    · simp only [List.filter_cons, ha, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at h
      simp only [addMissing, ha, ↓reduceIte]
      exact ih pre post h hp
    · simp only [List.filter_cons, ha, not_false_eq_true, decide_true, ↓reduceIte] at h
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, _⟩ := h
        simp [addMissing, ha, hs, bind, Except.bind]
      | cons q t =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨he, h2⟩ := h
        subst he
        have h1 := hp (a, b) (by simp)
        have h3 := ih t post h2 (fun p hq => hp p (by simp [hq]))
        simp only at h1
        simp [addMissing, ha, h1, h3, bind, Except.bind]

/-- `total_ordering`, exactly. The root is the greatest name of the roots, so that replacing `max` fails this; what goes in
is `_convert[root]` less the roots, each name with its own function, which `TotalOrderingCorrect` says computes the right
thing; and a refused `setattr` escapes after those before it, from where it stands in `_convert[root]`. -/
def TotalOrderingExact : Prop :=
  ∀ (c : OrdClass) (roots : List OrdOp) (root : OrdOp), rootsOf c ordOps = .ok roots → maxRoot roots = some root →
    root ∈ roots ∧ (∀ o ∈ roots, ¬ (root.name < o.name)) ∧
    ((∀ o s, c.setAttr o s = .ok ()) →
      totalOrdering c = .ok (root, (convert root).filter (fun p => decide (p.1 ∉ roots)))) ∧
    (∀ pre o s post e, (convert root).filter (fun p => decide (p.1 ∉ roots)) = pre ++ (o, s) :: post →
      (∀ p ∈ pre, c.setAttr p.1 p.2 = .ok ()) → c.setAttr o s = .error e → totalOrdering c = .error e)

theorem totalOrderingExact_proven : TotalOrderingExact := by
  intro c roots root hr hm
  obtain ⟨h1, h2⟩ := maxRoot_is_max roots root hm
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hs
    simp only [totalOrdering, hr, hm, addMissing_ok c roots hs, bind, Except.bind, pure, Except.pure]
    first | rfl | skip
  · intro pre o s post e h3 h4 h5
    have := addMissing_refused c roots o s e h5 (convert root) pre post h3 h4
    simp only [totalOrdering, hr, hm, this, bind, Except.bind]
    first | rfl | skip

end PyLean.CoreLibs.Functools
