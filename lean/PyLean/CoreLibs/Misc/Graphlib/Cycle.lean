import PyLean.CoreLibs.Misc.Graphlib.Model

/-!
`_find_cycle`: what it reports is a real cycle, and when it reports nothing the graph has none. The
second half is the classic depth-first argument. `ord` is a ghost list of the finished nodes, newest
first, and every successor of a finished node lies behind it in `ord` (`Chain`).
-/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

variable {α : Type} [DecidableEq α]

/-- `b` is a successor of `a`, the edge `a -> b` of the working graph. -/
def Edge (m : List (NodeInfo α)) (a b : α) : Prop := b ∈ succs m a

/-- Each element is an immediate predecessor of the next, as the docstring of `CycleError` says. -/
def IsPath (m : List (NodeInfo α)) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => Edge m a b ∧ IsPath m (b :: r)

theorem IsPath.snoc {m : List (NodeInfo α)} {x y : α} :
    ∀ (l : List α), IsPath m (l ++ [x]) → Edge m x y → IsPath m (l ++ [x] ++ [y]) := by
  intro l
  induction l with
  | nil => intro _ h; exact ⟨h, trivial⟩
  | cons a r ih =>
    intro hp he
    cases r with
    | nil => exact ⟨hp.1, ih hp.2 he⟩
    | cons b t => exact ⟨hp.1, ih hp.2 he⟩

/-- The frames are linked: each frame's node is an edge to the frame above it, and `next` is the
node the top frame's iterator produced. -/
def LinkF (m : List (NodeInfo α)) : Option α → List (α × List α) → Prop
  | _, [] => True
  | nxt, (n, rem) :: fr =>
    (∀ y, nxt = some y → y ∈ succs m n) ∧ (∀ y ∈ rem, y ∈ succs m n) ∧ LinkF m (some n) fr

theorem LinkF.weaken {m : List (NodeInfo α)} {x : Option α} :
    ∀ {fr : List (α × List α)}, LinkF m x fr → LinkF m none fr := by
  intro fr h
  cases fr with
  | nil => trivial
  | cons p r =>
    obtain ⟨n, rem⟩ := p
    exact ⟨fun _ e => (by cases e), h.2.1, h.2.2⟩

theorem backtrack_link {m : List (NodeInfo α)} :
    ∀ (fr : List (α × List α)) (s : α) (fr' : List (α × List α)), LinkF m none fr →
      backtrack fr = some (s, fr') → LinkF m (some s) fr' := by
  intro fr
  induction fr with
  | nil => intro s fr' _ h; simp [backtrack] at h
  | cons p r ih =>
    intro s fr' hl h
    obtain ⟨n, rem⟩ := p
    cases rem with
    | nil =>
      simp only [backtrack] at h
      exact ih s fr' hl.2.2.weaken h
    | cons a t =>
      simp only [backtrack, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_, hl.2.2⟩
      · intro y e
        cases e
        exact hl.2.1 _ (by simp)
      · intro y hy
        exact hl.2.1 y (by simp [hy])

theorem cycleOf_path {m : List (NodeInfo α)} (node : α) :
    ∀ (fr : List (α × List α)) (last : α), LinkF m (some last) fr → node ∈ fr.map (·.1) →
      IsPath m (node :: ((fr.map (·.1)).takeWhile (· ≠ node)).reverse ++ [last]) := by
  intro fr
  induction fr with
  | nil => intro last _ h; simp at h
  | cons p r ih =>
    intro last hl hm
    obtain ⟨n, rem⟩ := p
    by_cases hn : n = node
    · subst hn
      simp only [List.map_cons, List.takeWhile_cons, ne_eq, not_true_eq_false, decide_false,
        cond_false, List.reverse_nil, List.nil_append]
      exact ⟨hl.1 _ rfl, trivial⟩
    · have hm' : node ∈ r.map (·.1) := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm hn
        · exact h
      have hi := ih n hl.2.2 hm'
      simp only [List.map_cons, List.takeWhile_cons]
      simp only [ne_eq, hn, not_false_eq_true, decide_true, cond_true, List.reverse_cons]
      have := IsPath.snoc (m := m) (x := n) (y := last)
        (node :: ((r.map (·.1)).takeWhile (· ≠ node)).reverse) (by simpa using hi) (hl.1 _ rfl)
      simpa [List.append_assoc] using this

/-- A `cycleOf` result is a closed path. -/
def IsCycle (m : List (NodeInfo α)) (c : List α) : Prop :=
  2 ≤ c.length ∧ c.head? = c.getLast? ∧ IsPath m c

theorem walk_cycle (m : List (NodeInfo α)) :
    ∀ (fuel : Nat) (node : α) (fr : List (α × List α)) (seen c : List α),
      LinkF m (some node) fr →
      walk m fuel node fr seen = .ok (.inr c) → IsCycle m c := by
  intro fuel
  induction fuel with
  | zero => intro node fr seen c _ h; simp [walk] at h
  | succ f ih =>
    intro node fr seen c hl h
    simp only [walk] at h
    split at h
    · split at h
      · rename_i hm
        simp only [Except.ok.injEq, Sum.inr.injEq] at h
        subst h
        have hp := cycleOf_path node fr node hl hm
        have e : cycleOf fr node =
            (node :: ((fr.map (·.1)).takeWhile (· ≠ node)).reverse) ++ [node] := rfl
        refine ⟨by simp [cycleOf], ?_, hp⟩
        rw [e, List.getLast?_concat]
        rfl
      · split at h
        · rename_i n' fr' hb
          exact ih n' fr' seen c (backtrack_link fr n' fr' hl.weaken hb) h
        · simp at h
    · split at h
      · rename_i n' fr' hb
        refine ih n' fr' _ c (backtrack_link _ n' fr' ?_ hb) h
        exact ⟨fun _ e => (by cases e), fun _ h => h, hl⟩
      · simp at h

theorem forNodes_cycle (m : List (NodeInfo α)) :
    ∀ (l : List (NodeInfo α)) (seen c : List α), forNodes m l seen = .ok (some c) → IsCycle m c := by
  intro l
  induction l with
  | nil => intro seen c h; simp [forNodes] at h
  | cons i rest ih =>
    intro seen c h
    simp only [forNodes] at h
    split at h
    · exact ih _ _ h
    · split at h
      · simp at h
      · rename_i c' hw
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact walk_cycle m _ i.node [] seen _ trivial hw
      · exact ih _ _ h

/-- `CycleError`: "The detected cycle ... consists in a list of nodes, such that each node is, in
the graph, an immediate predecessor of the next node in the list. In the reported list, the first and
the last node will be the same". For every graph, what `_find_cycle` returns has that form. -/
def FindCycleSound : Prop :=
  ∀ (α : Type) [DecidableEq α] (m : List (NodeInfo α)) (c : List α),
    findCycle m = .ok (some c) → IsCycle m c

theorem findCycleSound_proven : FindCycleSound := by
  intro α _ m c h
  exact forNodes_cycle m m [] c h

/-! ### No report means no cycle -/

/-- Finished nodes, newest first: the successors of each lie behind it. -/
def Chain (m : List (NodeInfo α)) : List α → Prop
  | [] => True
  | x :: t => (∀ y ∈ succs m x, y ∈ t) ∧ Chain m t

/-- What the frames still owe: a successor is unconsumed, finished, or the node just produced. -/
def FrOK (m : List (NodeInfo α)) (ord : List α) : Option α → List (α × List α) → Prop
  | _, [] => True
  | c, (n, rem) :: fr =>
    (∀ y ∈ succs m n, y ∈ rem ∨ y ∈ ord ∨ c = some y) ∧ FrOK m ord (some n) fr

theorem FrOK.mono {m : List (NodeInfo α)} {ord ord' : List α} (h : ∀ x ∈ ord, x ∈ ord') :
    ∀ {c : Option α} {fr : List (α × List α)}, FrOK m ord c fr → FrOK m ord' c fr := by
  intro c fr hf
  induction fr generalizing c with
  | nil => trivial
  | cons p r ih =>
    obtain ⟨n, rem⟩ := p
    refine ⟨?_, ih hf.2⟩
    intro y hy
    rcases hf.1 y hy with a | a | a
    · exact .inl a
    · exact .inr (.inl (h _ a))
    · exact .inr (.inr a)

/-- The invariant of the depth-first search. -/
structure WInv (m : List (NodeInfo α)) (ord : List α) (fr : List (α × List α)) (seen : List α) :
    Prop where
  seenSub : ∀ x ∈ seen, x ∈ ord ∨ x ∈ fr.map (·.1)
  ordSeen : ∀ x ∈ ord, x ∈ seen
  frSeen : ∀ x ∈ fr.map (·.1), x ∈ seen
  chain : Chain m ord
  nodup : ord.Nodup
  frNodup : (fr.map (·.1)).Nodup
  disj : ∀ x ∈ ord, x ∉ fr.map (·.1)

theorem backtrack_inv {m : List (NodeInfo α)} (seen : List α) :
    ∀ (fr : List (α × List α)) (ord : List α), WInv m ord fr seen → FrOK m ord none fr →
      match backtrack fr with
      | none => ∃ ord', WInv m ord' [] seen ∧ ∀ x ∈ ord, x ∈ ord'
      | some (s, fr') => ∃ ord', WInv m ord' fr' seen ∧ FrOK m ord' (some s) fr' ∧
          ∀ x ∈ ord, x ∈ ord' := by
  intro fr
  induction fr with
  | nil => intro ord h _; exact ⟨ord, h, fun _ h => h⟩
  | cons p r ih =>
    intro ord hw hf
    obtain ⟨n, rem⟩ := p
    cases rem with
    | cons a t =>
      simp only [backtrack]
      refine ⟨ord, ?_, ?_, fun _ h => h⟩
      · exact { seenSub := by simpa using hw.seenSub, ordSeen := hw.ordSeen,
                frSeen := by simpa using hw.frSeen, chain := hw.chain, nodup := hw.nodup,
                frNodup := by simpa using hw.frNodup, disj := by simpa using hw.disj }
      · refine ⟨?_, hf.2⟩
        intro y hy
        rcases hf.1 y hy with h | h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (.inr rfl)
          · exact .inl h
        · exact .inr (.inl h)
        · cases h
    | nil =>
      simp only [backtrack]
      have hn : n ∉ ord := fun h => hw.disj n h (by simp)
      have hnr : n ∉ r.map (·.1) := by
        have := hw.frNodup
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1
      have hsucc : ∀ y ∈ succs m n, y ∈ ord := by
        intro y hy
        rcases hf.1 y hy with h | h | h
        · simp at h
        · exact h
        · cases h
      have hw' : WInv m (n :: ord) r seen :=
        { seenSub := by
            intro x hx
            rcases hw.seenSub x hx with h | h
            · exact .inl (by simp [h])
            · simp only [List.map_cons, List.mem_cons] at h
              rcases h with rfl | h
              · exact .inl (by simp)
              · exact .inr h
          ordSeen := by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | h
            · exact hw.frSeen _ (by simp)
            · exact hw.ordSeen x h
          frSeen := fun x hx => hw.frSeen x (by simp [hx])
          chain := ⟨hsucc, hw.chain⟩
          nodup := List.nodup_cons.2 ⟨hn, hw.nodup⟩
          frNodup := (List.nodup_cons.1 hw.frNodup).2
          disj := by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | h
            · exact hnr
            · exact fun h2 => hw.disj x h (by simp [h2]) }
      have hf' : FrOK m (n :: ord) none r := by
        have h1 : FrOK m (n :: ord) (some n) r := FrOK.mono (fun x h => by simp [h]) hf.2
        cases r with
        | nil => trivial
        | cons q t =>
          obtain ⟨u, rem⟩ := q
          refine ⟨?_, h1.2⟩
          intro y hy
          rcases h1.1 y hy with a | a | a
          · exact .inl a
          · exact .inr (.inl a)
          · simp only [Option.some.injEq] at a
            exact .inr (.inl (by simp [a]))
      have := ih (n :: ord) hw' hf'
      cases hb : backtrack r with
      | none =>
        rw [hb] at this
        obtain ⟨o', h1, h2⟩ := this
        exact ⟨o', h1, fun x hx => h2 x (by simp [hx])⟩
      | some q =>
        obtain ⟨s, fr'⟩ := q
        rw [hb] at this
        obtain ⟨o', h1, h2, h3⟩ := this
        exact ⟨o', h1, h2, fun x hx => h3 x (by simp [hx])⟩

theorem walk_inv (m : List (NodeInfo α)) :
    ∀ (fuel : Nat) (node : α) (fr : List (α × List α)) (seen seen' ord : List α),
      WInv m ord fr seen → FrOK m ord (some node) fr →
      walk m fuel node fr seen = .ok (.inl seen') →
      ∃ ord', WInv m ord' [] seen' ∧ (∀ x ∈ ord, x ∈ ord') ∧ node ∈ ord' := by
  intro fuel
  induction fuel with
  | zero => intro node fr seen seen' ord _ _ h; simp [walk] at h
  | succ f ih =>
    intro node fr seen seen' ord hw hf h
    simp only [walk] at h
    split at h
    · rename_i hs
      split at h
      · simp at h
      · rename_i hnf
        have hno : node ∈ ord := (hw.seenSub node hs).resolve_right hnf
        have hf0 : FrOK m ord none fr := by
          cases fr with
          | nil => trivial
          | cons q t =>
            obtain ⟨u, rem⟩ := q
            refine ⟨?_, hf.2⟩
            intro y hy
            rcases hf.1 y hy with a | a | a
            · exact .inl a
            · exact .inr (.inl a)
            · simp only [Option.some.injEq] at a
              subst a
              exact .inr (.inl hno)
        have hb := backtrack_inv seen fr ord hw hf0
        split at h
        · rename_i n' fr' hbk
          rw [hbk] at hb
          obtain ⟨o', h1, h2, h3⟩ := hb
          obtain ⟨o'', c1, c2, _⟩ := ih n' fr' seen seen' o' h1 h2 h
          exact ⟨o'', c1, fun x hx => c2 x (h3 x hx), c2 _ (h3 _ hno)⟩
        · rename_i hbk
          rw [hbk] at hb
          simp only [Except.ok.injEq, Sum.inl.injEq] at h
          subst h
          obtain ⟨o', h1, h2⟩ := hb
          exact ⟨o', h1, h2, h2 _ hno⟩
    · rename_i hs
      have hord : node ∉ ord := fun h => hs (hw.ordSeen node h)
      have hfrn : node ∉ fr.map (·.1) := fun h => hs (hw.frSeen node h)
      have hw1 : WInv m ord ((node, succs m node) :: fr) (node :: seen) :=
        { seenSub := by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | h
            · exact .inr (by simp)
            · rcases hw.seenSub x h with a | a
              · exact .inl a
              · exact .inr (by simp [a])
          ordSeen := fun x hx => by simp [hw.ordSeen x hx]
          frSeen := by
            intro x hx
            simp only [List.map_cons, List.mem_cons] at hx
            rcases hx with rfl | h
            · simp
            · simp [hw.frSeen x h]
          chain := hw.chain
          nodup := hw.nodup
          frNodup := by simpa [hfrn] using hw.frNodup
          disj := by
            intro x hx h2
            simp only [List.map_cons, List.mem_cons] at h2
            rcases h2 with rfl | h2
            · exact hord hx
            · exact hw.disj x hx h2 }
      have hf1 : FrOK m ord none ((node, succs m node) :: fr) :=
        ⟨fun y hy => .inl hy, hf⟩
      have hb := backtrack_inv (node :: seen) _ ord hw1 hf1
      split at h
      · rename_i n' fr' hbk
        rw [hbk] at hb
        obtain ⟨o', h1, h2, h3⟩ := hb
        obtain ⟨o'', c1, c2, _⟩ := ih n' fr' _ seen' o' h1 h2 h
        refine ⟨o'', c1, fun x hx => c2 x (h3 x hx), ?_⟩
        -- `node` is on the stack, hence finished by the end
        have hseen : node ∈ seen' := by
          have hmono : ∀ (f : Nat) (a : α) (fr : List (α × List α)) (s s' : List α),
              walk m f a fr s = .ok (.inl s') → ∀ x ∈ s, x ∈ s' := by
            intro f
            induction f with
            | zero => intro a fr s s' h; simp [walk] at h
            | succ g ihg =>
              intro a fr s s' h x hx
              simp only [walk] at h
              split at h
              · split at h
                · simp at h
                · split at h
                  · exact ihg _ _ _ _ h x hx
                  · simp only [Except.ok.injEq, Sum.inl.injEq] at h
                    subst h
                    exact hx
              · split at h
                · exact ihg _ _ _ _ h x (by simp [hx])
                · simp only [Except.ok.injEq, Sum.inl.injEq] at h
                  subst h
                  simp [hx]
          exact hmono f n' fr' _ _ h node (by simp)
        have := c1.seenSub node hseen
        simpa using this
      · rename_i hbk
        rw [hbk] at hb
        simp only [Except.ok.injEq, Sum.inl.injEq] at h
        subst h
        obtain ⟨o', h1, h2⟩ := hb
        refine ⟨o', h1, h2, ?_⟩
        have := h1.seenSub node (by simp)
        simpa using this

theorem forNodes_inv (m : List (NodeInfo α)) :
    ∀ (l : List (NodeInfo α)) (seen ord : List α), WInv m ord [] seen →
      forNodes m l seen = .ok none →
      ∃ ord', Chain m ord' ∧ ord'.Nodup ∧ (∀ i ∈ l, i.node ∈ ord') ∧ ∀ x ∈ ord, x ∈ ord' := by
  intro l
  induction l with
  | nil => intro seen ord hw _; exact ⟨ord, hw.chain, hw.nodup, by simp, fun _ h => h⟩
  | cons i rest ih =>
    intro seen ord hw h
    simp only [forNodes] at h
    split at h
    · rename_i hs
      obtain ⟨o', a, b, c, d⟩ := ih seen ord hw h
      refine ⟨o', a, b, ?_, d⟩
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · have := hw.seenSub _ hs
        simp only [List.map_nil, List.not_mem_nil, or_false] at this
        exact d _ this
      · exact c j hj
    · split at h
      · simp at h
      · simp at h
      · rename_i seen2 hwk
        obtain ⟨o2, w2, m2, n2⟩ := walk_inv m _ i.node [] seen seen2 ord hw trivial hwk
        obtain ⟨o', a, b, c, d⟩ := ih seen2 o2 w2 h
        refine ⟨o', a, b, ?_, fun x hx => d x (m2 x hx)⟩
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact d _ n2
        · exact c j hj

/-- A topological certificate for `m`, from a `_find_cycle` that returned `None`. -/
theorem findCycle_none (m : List (NodeInfo α)) (h : findCycle m = .ok none) :
    ∃ ord, Chain m ord ∧ ord.Nodup ∧ ∀ i ∈ m, i.node ∈ ord := by
  have hw : WInv m [] [] [] :=
    { seenSub := by simp, ordSeen := by simp, frSeen := by simp, chain := trivial,
      nodup := List.nodup_nil, frNodup := List.nodup_nil, disj := by simp }
  obtain ⟨o, a, b, c, _⟩ := forNodes_inv m m [] [] hw h
  exact ⟨o, a, b, c⟩

theorem n2iGet_mem {m : List (NodeInfo α)} {k : α} {i : NodeInfo α} (h : n2iGet m k = some i) :
    i ∈ m ∧ i.node = k := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨h2, by simpa using h1⟩

/-- A node with a successor is a node of `m`. -/
theorem edge_key {m : List (NodeInfo α)} {a b : α} (h : Edge m a b) : ∃ i ∈ m, i.node = a := by
  unfold Edge succs at h
  cases hg : n2iGet m a with
  | none => simp [hg] at h
  | some i =>
    obtain ⟨h1, h2⟩ := n2iGet_mem hg
    exact ⟨i, h1, h2⟩

theorem chain_tail_mem {m : List (NodeInfo α)} :
    ∀ (l : List α) (x y : α), Chain m l → x ∈ l → y ∈ succs m x → y ∈ l := by
  intro l
  induction l with
  | nil => intro x y _ h; simp at h
  | cons a t ih =>
    intro x y hc hx hy
    rcases List.mem_cons.1 hx with rfl | h
    · exact List.mem_cons_of_mem _ (hc.1 y hy)
    · exact List.mem_cons_of_mem _ (ih x y hc.2 h hy)

theorem chain_idx {m : List (NodeInfo α)} :
    ∀ (l : List α) (x y : α), Chain m l → l.Nodup → x ∈ l → y ∈ succs m x →
      l.idxOf x < l.idxOf y := by
  intro l
  induction l with
  | nil => intro x y _ _ h; simp at h
  | cons a t ih =>
    intro x y hc hn hx hy
    have hnt := List.nodup_cons.1 hn
    by_cases hax : a = x
    · subst hax
      have hyt : y ∈ t := hc.1 y hy
      have hne : a ≠ y := fun e => hnt.1 (e ▸ hyt)
      simp [List.idxOf_cons, hne]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hax
        · exact h
      have hyt : y ∈ t := chain_tail_mem t x y hc.2 hxt hy
      have hne : a ≠ y := fun e => hnt.1 (e ▸ hyt)
      have := ih x y hc.2 hnt.2 hxt hy
      simp [List.idxOf_cons, hax, hne]
      omega

theorem path_idx {m : List (NodeInfo α)} (ord : List α) (hc : Chain m ord) (hn : ord.Nodup) :
    ∀ (p : List α) (a : α), IsPath m (a :: p) → a ∈ ord → p ≠ [] →
      ord.idxOf a < ord.idxOf (p.getLast?.getD a) ∧ (p.getLast?.getD a) ∈ ord := by
  intro p
  induction p with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons b t ih =>
    intro a hp ha _
    have hab := chain_idx ord a b hc hn ha hp.1
    have hbm := chain_tail_mem ord a b hc ha hp.1
    cases t with
    | nil => simpa using ⟨hab, hbm⟩
    | cons c u =>
      obtain ⟨h1, h2⟩ := ih b hp.2 hbm (by simp)
      have h0 : (b :: c :: u).getLast? = (c :: u).getLast? := by simp [List.getLast?_cons_cons]
      rw [h0]
      cases hl : (c :: u).getLast? with
      | none => simp at hl
      | some w =>
        rw [hl] at h1 h2
        simp only [Option.getD_some] at h1 h2 ⊢
        exact ⟨by omega, h2⟩

/-- `prepare` does not miss a cycle: when `_find_cycle` returns `None` the graph has no closed path. -/
def NoReportNoCycle : Prop :=
  ∀ (α : Type) [DecidableEq α] (m : List (NodeInfo α)),
    findCycle m = .ok none → ∀ c, ¬ IsCycle m c

theorem noReportNoCycle_proven : NoReportNoCycle := by
  intro α _ m h c hc
  obtain ⟨ord, h1, h2, h3⟩ := findCycle_none m h
  obtain ⟨hl, he, hp⟩ := hc
  cases c with
  | nil => simp at hl
  | cons a t =>
    cases t with
    | nil => simp at hl
    | cons b u =>
      obtain ⟨i, hi, hn⟩ := edge_key hp.1
      have ha : a ∈ ord := hn ▸ h3 i hi
      obtain ⟨g1, _⟩ := path_idx ord h1 h2 (b :: u) a hp ha (by simp)
      have e2 : (b :: u).getLast?.getD a = a := by
        have : (a :: b :: u).getLast? = (b :: u).getLast? := by simp [List.getLast?_cons_cons]
        rw [← this, ← he]
        rfl
      rw [e2] at g1
      omega

end PyLean.CoreLibs.Misc.Graphlib
