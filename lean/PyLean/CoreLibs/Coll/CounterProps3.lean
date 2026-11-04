import PyLean.CoreLibs.Coll.CounterProps2

/-!
Properties of the generic `Counter` model, continued: the multiset operators, `_keep_positive`,
the in-place operators, `update`, `subtract`, the constructor and `__repr__`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Eff SEnv Sorter HO hEnv nSelect pySortedBy pureKey builtinHier Hier isA SortOk)

variable {κ ν : Type} [DecidableEq κ]

/-- The items a `result[elem] = value` loop stores from `l`. -/
def stored (F : κ → ν → Option ν) (l : D κ ν) : D κ ν :=
  l.filterMap (fun p => (F p.1 p.2).map (fun v => (p.1, v)))

theorem keys_stored_sub {F : κ → ν → Option ν} {a : D κ ν} {x : κ} (h : x ∈ D.keys (stored F a)) :
    x ∈ D.keys a := by
  simp only [stored, D.keys, List.mem_map, List.mem_filterMap] at h ⊢
  obtain ⟨q, ⟨p, hp, hq⟩, rfl⟩ := h
  cases hF : F p.1 p.2 with
  | none => simp [hF] at hq
  | some v =>
    simp [hF] at hq
    exact ⟨p, hp, by rw [← hq]⟩

/-- `elem not in self and f(count)`, as the operators' second loop decides it. -/
def rightOf (a : D κ ν) (f : ν → Option ν) (e : κ) (c : ν) : Option ν := if D.mem a e then none else f c

theorem fresh_right (a b : D κ ν) (F : κ → ν → Option ν) (f : ν → Option ν) :
    ∀ p ∈ b, (rightOf a f p.1 p.2).isSome →
      p.1 ∉ D.keys ([] ++ a.filterMap (fun p => (F p.1 p.2).map (fun v => (p.1, v)))) := by
  intro p _ hs hk
  simp only [List.nil_append] at hk
  have hm := keys_stored_sub (F := F) hk
  simp only [rightOf] at hs
  rw [(D.mem_iff).2 hm] at hs
  simp at hs

/-- **The multiset operators, pointwise.** For every key type and every count type whose `+`,
`-`, `<` and `>` (with their truth tests) are pure functions `A`, `S`, `LT`, `GT` (any
functions: non-commutative sums, partial orders, NaN-like values): `a + b`, `a - b`, `a | b`
and `a & b` store, in `a`'s order, each key of `a` with `a[e] + b[e]`, `a[e] - b[e]`, the
larger or the smaller of `a[e]`, `b[e]` (`<` decides; `b[e]` is `0` when missing) whenever
that is `> 0`, and then, for `+`, `-` and `|`, in `b`'s order, each key of `b` not in `a` with
`b[e]` when `b[e] > 0` (`0 - b[e]` when `b[e] < 0` for `-`). Against a non-`Counter` operand
each returns `NotImplemented`.

Source: docstrings and comments, Lib/collections/__init__.py:765-772, :836-908. -/
def OperatorsPointwise : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (N : Num ν) (A S : ν → ν → ν) (LT GT : ν → ν → Bool)
    (a b : D κ ν), D.WF a → D.WF b → HashOk K a → HashOk K b →
    N.add = (fun x y => .ok (A x y)) → N.sub = (fun x y => .ok (S x y)) →
    N.lt = (fun x y => .ok (LT x y)) → N.gt = (fun x y => .ok (GT x y)) →
    let pos := fun (n : ν) => if GT n N.zero then some n else none
    addC K N a b = .ok (stored (fun e c => pos (A c (at0 N b e))) a ++ stored (rightOf a pos) b) ∧
    subC K N a b = .ok (stored (fun e c => pos (S c (at0 N b e))) a ++
      stored (rightOf a (fun c => if LT c N.zero then some (S N.zero c) else none)) b) ∧
    orC K N a b = .ok (stored (fun e c => pos (if LT c (at0 N b e) then at0 N b e else c)) a ++
      stored (rightOf a pos) b) ∧
    andC K N a b = .ok (stored (fun e c => pos (if LT c (at0 N b e) then c else at0 N b e)) a) ∧
    (∀ f ∈ [addC K N a, subC K N a, orC K N a, andC K N a],
      guarded f .other = none ∧ guarded f (.ctr b) = some (f b))

theorem operatorsPointwise_proven : OperatorsPointwise := by
  intro κ ν _ K N A S LT GT a b wa wb ha hb hA hS hL hG
  simp only
  have right_pos : ∀ p ∈ b, onlyRightPos K N a p.1 p.2 =
      .ok (rightOf a (fun n => if GT n N.zero then some n else none) p.1 p.2) := by
    intro p hp
    unfold onlyRightPos
    rw [dMem_ok a (hash_of_mem hb hp), ok_bind]
    cases hm : D.mem a p.1 <;> simp [rightOf, hm, hG]
  refine ⟨?_, ?_, ?_, ?_, fun f _ => ⟨rfl, rfl⟩⟩
  · unfold addC
    rw [loopInto_pure K (F := fun e c => if GT (A c (at0 N b e)) N.zero then some (A c (at0 N b e)) else none)
      a [] wa ha (by simp)]
    · rw [ok_bind]
      refine (loopInto_pure K b _ wb hb (fresh_right a b (fun e c => if GT (A c (at0 N b e)) N.zero then some (A c (at0 N b e)) else none) _) right_pos).trans ?_
      rfl
    · intro p hp
      rw [dGet_ok b N.zero (hash_of_mem ha hp)]
      simp only [hA, hG, ok_bind, pure_py]; rfl
  · unfold subC
    rw [loopInto_pure K (F := fun e c => if GT (S c (at0 N b e)) N.zero then some (S c (at0 N b e)) else none)
      a [] wa ha (by simp)]
    · rw [ok_bind]
      refine (loopInto_pure K (F := rightOf a (fun c => if LT c N.zero then some (S N.zero c) else none))
        b _ wb hb (fresh_right a b (fun e c => if GT (S c (at0 N b e)) N.zero then some (S c (at0 N b e)) else none) _) ?_).trans ?_
      · intro p hp
        rw [dMem_ok a (hash_of_mem hb hp), ok_bind]
        cases hm : D.mem a p.1
        · cases hl : LT p.2 N.zero <;> simp [rightOf, hm, hL, hS, hl]
        · simp [rightOf, hm]
      · rfl
    · intro p hp
      rw [dGet_ok b N.zero (hash_of_mem ha hp)]
      simp only [hS, hG, ok_bind, pure_py]; rfl
  · unfold orC
    rw [loopInto_pure K
      (F := fun e c => if GT (if LT c (at0 N b e) then at0 N b e else c) N.zero then
        some (if LT c (at0 N b e) then at0 N b e else c) else none)
      a [] wa ha (by simp)]
    · rw [ok_bind]
      refine (loopInto_pure K b _ wb hb (fresh_right a b (fun e c => if GT (if LT c (at0 N b e) then at0 N b e else c) N.zero then
        some (if LT c (at0 N b e) then at0 N b e else c) else none) _) right_pos).trans ?_
      rfl
    · intro p hp
      rw [dGet_ok b N.zero (hash_of_mem ha hp)]
      simp only [hL, hG, ok_bind, pure_py]; rfl
  · unfold andC
    refine (loopInto_pure K
      (F := fun e c => if GT (if LT c (at0 N b e) then c else at0 N b e) N.zero then
        some (if LT c (at0 N b e) then c else at0 N b e) else none)
      a [] wa ha (by simp) ?_).trans ?_
    · intro p hp
      rw [dGet_ok b N.zero (hash_of_mem ha hp)]
      simp only [hL, hG, ok_bind, pure_py]; rfl
    · rfl

/-! ### `_keep_positive` -/

theorem filterPy_pure {α : Type} {p : α → Py Bool} {P : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = .ok (P x)) → filterPy p l = .ok (l.filter P)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [filterPy, h x (by simp), ok_bind]
    rw [filterPy_pure xs (fun y hy => h y (by simp [hy])), ok_bind]
    cases hx : P x <;> simp [hx]

theorem del_eq_filter {d : D κ ν} (hw : D.WF d) (k : κ) : D.del d k = d.filter (fun q => decide (q.1 ≠ k)) := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    by_cases h : a = k
    · subst h
      have ht : t.filter (fun q => decide (q.1 ≠ a)) = t := by
        rw [List.filter_eq_self]
        intro q hq
        have hq1 := D.mem_keys_of_mem hq
        have : q.1 ≠ a := fun e => hn (by rw [e] at hq1; exact hq1)
        simpa using this
      simp only [D.del, if_pos rfl]
      simpa using ht.symm
    · simp [D.del, h, ih (D.WF_of_cons hw)]

theorem WF_filter {d : D κ ν} (hw : D.WF d) (P : κ × ν → Bool) : D.WF (d.filter P) := by
  unfold D.WF D.keys at *
  exact hw.sublist (List.Sublist.map _ (List.filter_sublist))

theorem foldl_del {l : D κ ν} : ∀ (d : D κ ν), D.WF d →
    l.foldl (fun s p => D.del s p.1) d = d.filter (fun q => decide (q.1 ∉ D.keys l)) := by
  induction l with
  | nil => intro d _; simp only [List.foldl_nil]; exact (List.filter_eq_self.2 (fun _ _ => by simp [D.keys])).symm
  | cons p l ih =>
    intro d hw
    simp only [List.foldl_cons]
    rw [del_eq_filter hw, ih _ (WF_filter hw _), List.filter_filter]
    congr 1
    funext q
    by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.1 ∈ D.keys l <;> simp_all [D.keys]

theorem mem_keys_filter_iff {d : D κ ν} (hw : D.WF d) {q : κ × ν} (hq : q ∈ d) (P : κ × ν → Bool) :
    q.1 ∈ D.keys (d.filter P) ↔ P q = true := by
  constructor
  · intro h
    simp only [D.keys, List.mem_map, List.mem_filter] at h
    obtain ⟨p, ⟨hp, hP⟩, he⟩ := h
    have h1 := D.get?_of_mem_pair hw hp
    have h2 := D.get?_of_mem_pair hw hq
    rw [he, h2] at h1
    have : p = q := by
      obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
      simp at he h1; subst he; subst h1; rfl
    rw [← this]; exact hP
  · intro h
    exact D.mem_keys_of_mem (List.mem_filter.2 ⟨hq, h⟩)

theorem stored_filter (G : ν → Bool) (d : D κ ν) :
    stored (fun _ c => if G c then some c else none) d = d.filter (fun p => G p.2) := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    cases hg : G v <;> simp [stored, hg] at ih ⊢ <;> exact ih

/-- **`_keep_positive` removes exactly the non-positive counts and is unary `+` in place.** For
every key type and every count type whose `>` (with its truth test) is a pure predicate `GT`
(NaN-like values with `not x > 0` included): `c._keep_positive()` leaves the items whose count is
`> 0`, in their order, and the same items `+c` returns.

Source: docstrings, Lib/collections/__init__.py:938, :957. -/
def KeepPositiveFilters : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (N : Num ν) (GT : ν → ν → Bool) (d : D κ ν),
    D.WF d → HashOk K d → N.gt = (fun x y => .ok (GT x y)) →
    keepPositive K rk N d = (d.filter (fun p => GT p.2 N.zero), none) ∧
    (keepPositive K rk N d).toPy = posC K N d

theorem keepPositiveFilters_proven : KeepPositiveFilters := by
  intro κ ν _ K rk N GT d hw hh hG
  have hk : keepPositive K rk N d = (d.filter (fun p => GT p.2 N.zero), none) := by
    unfold keepPositive
    rw [filterPy_pure (P := fun p => !GT p.2 N.zero) d (by intro p _; simp [hG])]
    simp only
    rw [loopS_pure (g := fun s p => D.del s p.1) _ d (by
      intro s p hp
      have hp' := (List.mem_filter.1 hp).1
      exact ((delitemGuard_proven κ ν K rk s p.1).1 (hash_of_mem hh hp')).1)]
    rw [foldl_del d hw]
    congr 1
    apply List.filter_congr
    intro q hq
    have := mem_keys_filter_iff hw hq (fun p => !GT p.2 N.zero)
    cases h : GT q.2 N.zero <;> simp_all
  refine ⟨hk, ?_⟩
  rw [hk]
  unfold posC
  rw [loopInto_pure K (F := fun _ c => if GT c N.zero then some c else none) d [] hw hh (by simp)
    (by intro p _; simp [hG])]
  show Out.toPy (d.filter _, none) =
    Except.ok ([] ++ stored (fun _ c => if GT c N.zero then some c else none) d)
  rw [List.nil_append, stored_filter]; rfl

/-! ### In-place operators -/

/-- **The in-place operators' operands.** For every key and count type: `+=`, `-=` and `|=` read
only `other.items()`, so a plain dict and a `Counter` with the same items give the same result;
an operand whose `.items()` raises (a non-mapping's `AttributeError`) raises it with `self`
unchanged. `&=` reads `other[elem]` for each key of `self` instead: on an empty counter it never
touches `other` (so `Counter() &= 5` succeeds), and with a plain dict missing the first key it
raises that `KeyError` with `self` unchanged.

Source: invariant; Lib/collections/__init__.py:972, :985, :998, :1013-1014. -/
def InplaceOperands : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (N : Num ν) (a b : D κ ν),
    iaddC K rk N a (ctrOpnd K N b) = iaddC K rk N a (dictOpnd K rk b) ∧
    isubC K rk N a (ctrOpnd K N b) = isubC K rk N a (dictOpnd K rk b) ∧
    iorC K rk N a (ctrOpnd K N b) = iorC K rk N a (dictOpnd K rk b) ∧
    (∀ (e : PyExc) (g : κ → Py ν),
      iaddC K rk N a ⟨.error e, g⟩ = (a, some e) ∧ isubC K rk N a ⟨.error e, g⟩ = (a, some e) ∧
      iorC K rk N a ⟨.error e, g⟩ = (a, some e)) ∧
    (∀ o : IOpnd κ ν, iandC K rk N [] o = ([], none)) ∧
    (∀ (k : κ) (v : ν) (t : D κ ν), K.hash k = .ok () → k ∉ D.keys b →
      iandC K rk N ((k, v) :: t) (dictOpnd K rk b) = ((k, v) :: t, some (.keyError (rk k))))

theorem inplaceOperands_proven : InplaceOperands := by
  intro κ ν _ K rk N a b
  refine ⟨rfl, rfl, rfl, fun e g => ⟨rfl, rfl, rfl⟩, fun o => rfl, fun k v t hk hn => ?_⟩
  have hg : D.get? b k = none := D.get?_eq_none_iff.2 hn
  simp [iandC, loopS, dictOpnd, dHash_ok hk, hg, Out.andThen]

/-! ### `update` with a `Mapping`: fast path and general loop -/

theorem loop_append {f : D κ ν → κ × ν → Py (D κ ν)} :
    ∀ (l s : D κ ν), D.WF (s ++ l) → (∀ s', ∀ p ∈ l, p.1 ∉ D.keys s' → f s' p = .ok (D.set s' p.1 p.2)) →
      loopS f s l = (s ++ l, none)
  | [], s, _, _ => by simp [loopS]
  | p :: l, s, hw, h => by
    have hn : p.1 ∉ D.keys s := by
      intro hm
      unfold D.WF at hw
      rw [D.keys_append] at hw
      exact (List.nodup_append.1 hw).2.2 _ hm _ (by simp [D.keys]) rfl
    simp only [loopS, h s p (by simp) hn, D.set_of_notMem p.2 hn]
    rw [loop_append l (s ++ [(p.1, p.2)]) (by simpa using hw) (fun s' q hq => h s' q (by simp [hq]))]
    simp

theorem loop_keys {g : D κ ν → κ → Py (D κ ν)} :
    ∀ (l s : D κ ν), D.WF (s ++ l) → (∀ s', ∀ p ∈ l, p.1 ∉ D.keys s' → g s' p.1 = .ok (D.set s' p.1 p.2)) →
      loopS g s (D.keys l) = (s ++ l, none)
  | [], s, _, _ => by simp [loopS, D.keys]
  | p :: l, s, hw, h => by
    have hn : p.1 ∉ D.keys s := by
      intro hm
      unfold D.WF at hw
      rw [D.keys_append] at hw
      exact (List.nodup_append.1 hw).2.2 _ hm _ (by simp [D.keys]) rfl
    show loopS g s (p.1 :: D.keys l) = _
    simp only [loopS, h s p (by simp) hn, D.set_of_notMem p.2 hn]
    rw [loop_keys l (s ++ [(p.1, p.2)]) (by simpa using hw) (fun s' q hq => h s' q (by simp [hq]))]
    simp

/-- **The empty-counter fast path of `update` agrees with the general loop.** For every key
type, every count type with `count + 0 == count`, and every `Mapping` with distinct hashable
keys whose `items()` yields what `dict.update` reads (its storage for a `dict`, `keys()` and
`m[k]` otherwise): on an empty counter, `update(m)` (the fast path, `dict.update`) leaves the
same items, in the same order, as the general `count + self_get(elem, 0)` loop, namely `m`'s.

Source: invariant, fast and slow path; comment 'fast path when counter is empty',
Lib/collections/__init__.py:704. -/
def UpdateFastSlow : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (N : Num ν) (m : MSrc κ ν) (L : D κ ν),
    D.WF L → HashOk K L → (∀ v, N.add v N.zero = .ok v) → m.items = .ok (FIt.ofList L) →
    (m.store = some L ∨ (m.store = none ∧ m.keys = .ok (D.keys L) ∧ ∀ p ∈ L, m.getitem p.1 = .ok p.2)) →
    updateMapping K N {} [] m = updateLoop K N {} [] m ∧ updateMapping K N {} [] m = (L, none)

theorem updateFastSlow_proven : UpdateFastSlow := by
  intro κ ν _ K N m L hw hh hadd hitems hsrc
  have hslow : updateLoop K N {} [] m = (L, none) := by
    unfold updateLoop
    rw [hitems]
    simp only [forPy, forIt, FIt.ofList]
    rw [loop_append L [] (by simpa using hw) (by
      intro s' p hp hn
      have hk := hash_of_mem hh hp
      dsimp only [boundGet, setItem]
      rw [dGet_ok s' N.zero hk, ok_bind, (D.get?_eq_none_iff).2 hn, Option.getD_none, hadd, ok_bind,
        dSet_ok s' p.2 hk])]
    simp
  have hfast : updateMapping K N {} [] m = (L, none) := by
    simp only [updateMapping, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, dictMerge]
    rcases hsrc with hs | ⟨hs, hk, hg⟩
    · rw [hs]; simp [update_nil_WF hw]
    · rw [hs, hk]
      simp only
      rw [loop_keys L [] (by simpa using hw) (by
        intro s' p hp hn
        rw [hg p hp, ok_bind, dSet_ok s' p.2 (hash_of_mem hh hp)])]
      simp
  exact ⟨hfast.trans hslow.symm, hfast⟩

/-! ### Counting an iterable, `subtract`, the constructor, on ints -/

/-- One counting step on ints. -/
def stepI (c : Int) (d : D κ Int) (x : κ) : D κ Int := D.set d x ((D.get? d x).getD 0 + c)

theorem get?_foldl_stepI (c : Int) (k : κ) :
    ∀ (xs : List κ) (d : D κ Int), D.get? (xs.foldl (stepI c) d) k =
      if k ∈ xs then some ((D.get? d k).getD 0 + c * (xs.count k : Int)) else D.get? d k
  | [], d => by simp
  | x :: xs, d => by
    simp only [List.foldl_cons]
    rw [get?_foldl_stepI c k xs]
    simp only [stepI, D.get?_set]
    by_cases hx : x = k
    · subst hx
      by_cases hm : x ∈ xs
      · simp [hm, List.count_cons_self, Int.mul_add] <;> omega
      · simp [hm, List.count_eq_zero_of_not_mem hm]
    · have hc : List.count k (x :: xs) = List.count k xs := by simp [List.count_cons, hx]
      simp [hx, Ne.symm hx, hc]

/-- The key order `dict.fromkeys(xs)` gives, after the keys already in `ks`. -/
def firstSeen (ks : List κ) (xs : List κ) : List κ :=
  xs.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) ks

theorem keys_foldl_stepI (c : Int) : ∀ (xs : List κ) (d : D κ Int),
    D.keys (xs.foldl (stepI c) d) = firstSeen (D.keys d) xs
  | [], _ => rfl
  | x :: xs, d => by
    simp only [List.foldl_cons, firstSeen]
    rw [keys_foldl_stepI c xs, stepI, D.keys_set]
    rfl

/-- **Counting an iterable of ints counts.** For every key type with hashable elements and every
iterator that yields `xs` and then stops or raises: `c.update(iterable)` adds to each key the
number of times it occurs in `xs`, appends the new keys in first-seen order, and raises what the
iterator raised, keeping the counts made before it (`_count_elements` on its fast path);
`c.subtract(iterable)` lowers the same counts by the same amounts and raises likewise, so
`subtract` after `update` restores every count. `Counter(iterable)` is that update of an empty
counter, or the exception.

Source: docstrings, Lib/collections/__init__.py:606-615, :678-688, :712-725, and
Doc/library/collections.rst ('in the order first encountered'). -/
def CountIterInt : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (K : KOps κ) (xs : List κ) (stop : Option PyExc) (d : D κ Int),
    (∀ k ∈ xs, K.hash k = .ok ()) →
    let it : Py (FIt κ) := .ok ⟨xs, stop⟩
    (∀ k, D.get? (update K intNum {} d (.iter it) []).1 k =
      if k ∈ xs then some ((D.get? d k).getD 0 + xs.count k) else D.get? d k) ∧
    D.keys (update K intNum {} d (.iter it) []).1 = firstSeen (D.keys d) xs ∧
    (update K intNum {} d (.iter it) []).2 = stop ∧
    (∀ k, D.get? (subtract K intNum {} d (.iter it) []).1 k =
      if k ∈ xs then some ((D.get? d k).getD 0 - xs.count k) else D.get? d k) ∧
    (subtract K intNum {} d (.iter it) []).2 = stop ∧
    (∀ k, D.get? (subtract K intNum {} (update K intNum {} d (.iter it) []).1 (.iter it) []).1 k =
      if k ∈ xs then some ((D.get? d k).getD 0) else D.get? d k) ∧
    counterNew K intNum (.iter it) [] = match stop with
      | none => .ok (xs.foldl (stepI 1) [])
      | some e => .error e

theorem update_iter_int (K : KOps κ) (xs : List κ) (stop : Option PyExc) (d : D κ Int)
    (hh : ∀ k ∈ xs, K.hash k = .ok ()) :
    update K intNum {} d (.iter (.ok ⟨xs, stop⟩)) [] = (xs.foldl (stepI 1) d, stop) := by
  have h1 : update K intNum {} d (.iter (.ok ⟨xs, stop⟩)) [] =
      (countCFast K intNum d ⟨xs, stop⟩).andThen (fun d => (d, none)) := rfl
  rw [h1]
  unfold countCFast forIt
  rw [loopS_pure (g := stepI 1) xs d (by
    intro s x hx
    rw [hh x hx, ok_bind]
    cases hg : D.get? s x <;> simp [stepI, hg, intNum])]
  cases stop <;> rfl

theorem subtract_iter_int (K : KOps κ) (xs : List κ) (stop : Option PyExc) (d : D κ Int)
    (hh : ∀ k ∈ xs, K.hash k = .ok ()) :
    subtract K intNum {} d (.iter (.ok ⟨xs, stop⟩)) [] = (xs.foldl (stepI (-1)) d, stop) := by
  unfold subtract subtractSrc forPy
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  unfold forIt
  rw [loopS_pure (g := stepI (-1)) xs d (by
    intro s x hx
    dsimp only [boundGet, setItem]
    rw [dGet_ok s _ (hh x hx), ok_bind]
    simp [stepI, intNum, dSet_ok _ _ (hh x hx), Int.sub_eq_add_neg])]
  cases stop <;> rfl

theorem countIterInt_proven : CountIterInt := by
  intro κ _ K xs stop d hh
  simp only
  rw [update_iter_int K xs stop d hh, subtract_iter_int K xs stop d hh,
    subtract_iter_int K xs stop _ hh]
  refine ⟨fun k => ?_, keys_foldl_stepI 1 xs d, rfl, fun k => ?_, rfl, fun k => ?_, ?_⟩
  · rw [get?_foldl_stepI]; simp
  · rw [get?_foldl_stepI]; by_cases hk : k ∈ xs <;> simp [hk] <;> omega
  · rw [get?_foldl_stepI, get?_foldl_stepI]
    by_cases hk : k ∈ xs <;> simp [hk] <;> omega
  · unfold counterNew
    rw [update_iter_int K xs stop [] hh]
    cases stop <;> rfl

end PyLean.CoreLibs.Coll
