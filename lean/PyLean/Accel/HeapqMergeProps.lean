import PyLean.Accel.HeapqSelectProps

/-!
`heapq.merge` (Lib/heapq.py:330-408) over the generator model of `HeapqSelect.lean`, with
honest inputs: input `i` is a re-iterable yielding `srcs[i]`, the comparisons are a strict weak
order with `==` its equivalence, and the key is pure. The world is the list of the inputs'
iterator positions.
-/

namespace PyLean.Accel.Heapq

open PyLean

/-- Input `i` and its iterator. -/
inductive MO where
  | src (i : Nat)
  | it (i : Nat)
  deriving DecidableEq

instance : Inhabited MO := ⟨.it 0⟩

variable {α : Type} [DecidableEq α] [Inhabited α]

def mEnv (srcs : List (List α)) (r : α → α → Bool) : SEnv (List Nat) α MO where
  lt a b := pure (r a b)
  gt a b := pure (r b a)
  eq a b := pure (!r a b && !r b a)
  iter o := match o with
    | .src i => ⟨fun w => (.ok (.it i), w.set i 0)⟩
    | .it i => pure (.it i)
  next o := match o with
    | .src _ => Eff.raise (.typeError "'list' object is not an iterator")
    | .it i => ⟨fun w => match (srcs.getD i [])[w.getD i 0]? with
      | some x => (.ok x, w.set i (w.getD i 0 + 1))
      | none => (.error .stopIteration, w)⟩
  len _ := Eff.raise (.typeError "object has no len()")
  toList o := match o with
    | .src i => pure (srcs.getD i [])
    | .it i => ⟨fun w => (.ok ((srcs.getD i []).drop (w.getD i 0)), w)⟩
  hier := builtinHier

def pureKeyG {W : Type} (κ : α → α) : α → Eff W PyExc α := fun x => pure (κ x)

/-- The entry order under the honest callbacks: key, then order, then (keyed lists) value. -/
def entLtP (r : α → α → Bool) (keyed : Bool) (x y : MEnt α MO) : Bool :=
  lexLt r (lexLt intLtB (fun a b => keyed && r a b)) (x.kv, x.order, x.value) (y.kv, y.order, y.value)

theorem strictWeak_keyedAnd {r : α → α → Bool} (hr : Accel.StrictWeak r) (keyed : Bool) :
    Accel.StrictWeak (fun a b => keyed && r a b) := by
  cases keyed
  · exact ⟨fun _ => rfl, fun _ _ _ h _ => h, fun _ _ _ h => by simp at h⟩
  · simpa using hr

theorem strictWeak_entLtP {r : α → α → Bool} (hr : Accel.StrictWeak r) (keyed : Bool) :
    Accel.StrictWeak (entLtP r keyed) :=
  StrictWeak.pullback (StrictWeak.lex hr (StrictWeak.lex strictWeak_intLtB (strictWeak_keyedAnd hr keyed)))
    (fun x : MEnt α MO => (x.kv, x.order, x.value))

theorem entLt_mEnv (srcs : List (List α)) (r : α → α → Bool) (hr : Accel.StrictWeak r) (keyed : Bool)
    (x y : MEnt α MO) : entLt (mEnv srcs r) keyed x y = pure (entLtP r keyed x y) := by
  obtain ⟨a, o, e, _⟩ := x; obtain ⟨b, o', e', _⟩ := y
  have htie : (if !keyed || decide (e = e') then (pure false : Eff (List Nat) PyExc Bool) else do
      let q ← (mEnv srcs r).eq e e'
      if q then pure false else (mEnv srcs r).lt e e') = pure (keyed && r e e') := by
    cases keyed
    · rfl
    · by_cases he : e = e'
      · subst he; simp [hr.irrefl]
      · simp only [Bool.not_true, Bool.false_or, he, decide_false, Bool.false_eq_true, if_false]
        show (pure (!r e e' && !r e' e) >>= _ : Eff (List Nat) PyExc Bool) = _
        rw [Eff.pure_bind]
        cases h1 : r e e' <;> cases h2 : r e' e <;> simp [mEnv, h1, h2]
  have hbo : (if o = o' then (if !keyed || decide (e = e') then (pure false : Eff (List Nat) PyExc Bool) else do
      let q ← (mEnv srcs r).eq e e'
      if q then pure false else (mEnv srcs r).lt e e') else pure (decide (o < o'))) =
      pure (lexLt intLtB (fun a b => keyed && r a b) (o, e) (o', e')) := by
    rw [lexInt_eq]
    by_cases ho : o = o'
    · simp only [if_pos ho, htie]
    · simp only [if_neg ho]
  simp only [entLt, entLtP]
  rw [hbo]
  simp only [lexLt]
  by_cases hab : a = b
  · subst hab
    simp [hr.irrefl]
  · simp only [if_neg hab]
    show (pure (!r a b && !r b a) >>= _ : Eff (List Nat) PyExc Bool) = _
    rw [Eff.pure_bind]
    cases h1 : r a b <;> cases h2 : r b a <;> simp [mEnv, h1, h2]

/-! ### The first `next()` -/

/-- The entry `merge` builds for input `i` (:366 / :390). -/
def entFor (srcs : List (List α)) (κ : Option (α → α)) (dir : Int) (i : Nat) : Option (MEnt α MO) :=
  (srcs.getD i []).head?.map (fun x => ⟨kOf κ x, (i : Int) * dir, x, .it i⟩)

theorem applyK_pureKeyG {W : Type} (κ : Option (α → α)) (x : α) :
    applyK (κ.map (pureKeyG (W := W))) x = pure (kOf κ x) := by
  cases κ <;> rfl

theorem mergeInit_mEnv (srcs : List (List α)) (r : α → α → Bool) (κ : Option (α → α)) (dir : Int) :
    ∀ (L : List Nat) (h : List (MEnt α MO)) (w : List Nat), (∀ i ∈ L, w.getD i 0 = 0) → L.Nodup →
      (mergeInit (mEnv srcs r) (κ.map pureKeyG) dir (L.map (fun i => (MO.src i, i))) h).run w =
        (.ok (h ++ L.filterMap (entFor srcs κ dir)),
          L.foldl (fun w i => w.set i (min 1 (srcs.getD i []).length)) w) := by
  intro L
  induction L with
  | nil => intro h w _ _; simp [mergeInit]
  | cons i L ih =>
    intro h w hw hnd
    have hi0 := hw i (by simp)
    have hwset : w.set i 0 = w := by
      apply List.ext_getElem (by simp)
      intro j h1 h2
      rw [List.getElem_set]
      split
      · subst_vars; have := hw j (by simp); simp [List.getD_eq_getElem?_getD, h2] at this; omega
      · rfl
    have hit : (Eff.attempt ((mEnv srcs r).iter (.src i))).run w = (.ok (.ok (.it i)), w) := by
      show (Except.ok (Except.ok (MO.it i)), w.set i 0) = _
      rw [hwset]
    simp only [List.map_cons, mergeInit]
    rw [Eff.run_bind_ok hit]
    simp only
    have hrest : ∀ j ∈ L, j ≠ i := fun j hj hji => by subst hji; exact (List.nodup_cons.1 hnd).1 hj
    have hnext : ((mEnv srcs r).next (.it i)).run w = match (srcs.getD i [])[0]? with
        | some x => (.ok x, w.set i 1)
        | none => (.error .stopIteration, w) := by
      show (match (srcs.getD i [])[w.getD i 0]? with
        | some x => ((Except.ok x : Except PyExc α), w.set i (w.getD i 0 + 1))
        | none => (Except.error PyExc.stopIteration, w)) = _
      rw [hi0]
    cases hs : (srcs.getD i [])[0]? with
    | none =>
      rw [hs] at hnext
      have hnil : srcs.getD i [] = [] := by
        cases hh : srcs.getD i [] with
        | nil => rfl
        | cons _ _ => rw [hh] at hs; cases hs
      have hat : (Eff.attempt (do
          let value ← (mEnv srcs r).next (.it i)
          let kv ← applyK (κ.map pureKeyG) value
          pure (MEnt.mk kv ((i : Int) * dir) value (MO.it i)))).run w = (.ok (.error .stopIteration), w) := by
        simp only [Eff.attempt]
        rw [Eff.run_bind_err hnext]
      rw [Eff.run_bind_ok hat]
      simp only
      rw [if_pos (show isA (mEnv srcs r).hier .stopIteration "StopIteration" = true from isA_stop),
        ih h w (fun j hj => hw j (by simp [hj])) (List.nodup_cons.1 hnd).2]
      simp only [List.filterMap_cons, entFor, hnil, List.head?_nil, Option.map_none, List.foldl_cons,
        List.length_nil, Nat.min_zero]
      rw [hwset]
    | some x =>
      rw [hs] at hnext
      have hat : (Eff.attempt (do
          let value ← (mEnv srcs r).next (.it i)
          let kv ← applyK (κ.map pureKeyG) value
          pure (MEnt.mk kv ((i : Int) * dir) value (MO.it i)))).run w =
          (.ok (.ok (MEnt.mk (kOf κ x) ((i : Int) * dir) x (MO.it i))), w.set i 1) := by
        simp only [Eff.attempt]
        rw [Eff.run_bind_ok hnext, applyK_pureKeyG]
        rfl
      rw [Eff.run_bind_ok hat]
      simp only
      have hw1 : ∀ j ∈ L, (w.set i 1).getD j 0 = 0 := by
        intro j hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
        rw [if_neg (Ne.symm (hrest j hj))]
        have := hw j (by simp [hj]); simpa [List.getD_eq_getElem?_getD] using this
      rw [ih _ _ hw1 (List.nodup_cons.1 hnd).2]
      have hlen : 1 ≤ (srcs.getD i []).length := by
        cases hh : srcs.getD i [] with
        | nil => rw [hh] at hs; cases hs
        | cons _ _ => simp
      have hhead : (srcs.getD i []).head? = some x := by
        rw [List.head?_eq_getElem?]; exact hs
      simp only [List.filterMap_cons, entFor, hhead, Option.map_some, List.foldl_cons, List.append_assoc,
        List.cons_append, List.nil_append]
      rw [Nat.min_eq_left hlen]

theorem foldl_set_range (srcs : List (List α)) :
    (List.range srcs.length).foldl (fun w i => w.set i (min 1 (srcs.getD i []).length)) (srcs.map (fun _ => 0)) =
      srcs.map (fun l => min 1 l.length) := by
  have key : ∀ k, k ≤ srcs.length →
      (List.range k).foldl (fun w i => w.set i (min 1 (srcs.getD i []).length)) (srcs.map (fun _ => 0)) =
        (srcs.zipIdx.map (fun p => if p.2 < k then min 1 p.1.length else 0)) := by
    intro k
    induction k with
    | zero => intro _; apply List.ext_getElem (by simp); intro j _ _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      rw [List.getElem_set]
      simp only [List.getElem_map, List.getElem_zipIdx]
      split
      · subst_vars; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < srcs.length by omega)]
      · rename_i hne
        by_cases hj : j < k
        · simp [hj, show j < k + 1 by omega]
        · have : ¬ j < k + 1 := by omega
          simp [hj, this]
  rw [key srcs.length (Nat.le_refl _)]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getElem_zipIdx]
  intro h; simp at h1; omega

theorem zipIdx_map_src (n : Nat) :
    ((List.range n).map MO.src).zipIdx = (List.range n).map (fun i => (MO.src i, i)) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getElem_zipIdx]

/-- **The first `next()` of `merge` is lazy and yields a smallest head.** For every element
type, strict weak order (with `==` its equivalence), pure key, `reverse`, and both heap
implementations: the first `next()` on `merge(*inputs, key=key, reverse=reverse)` pulls exactly
one item from each non-empty input (and nothing more), and yields one of those heads whose key
no other head's key is below (above, with `reverse=True`); with only empty inputs it is
exhausted at once. Source: the docstring (Lib/heapq.py:331-335: "does not pull the data into
memory all at once", "Merge multiple sorted inputs into a single sorted output"). -/
def MergeFirstNext : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (srcs : List (List α)) (r : α → α → Bool)
    (κ : Option (α → α)) (impl rev : Bool), Accel.StrictWeak r →
    let res := (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev ((List.range srcs.length).map MO.src)
      .start).run (srcs.map (fun _ => 0))
    res.2 = srcs.map (fun l => min 1 l.length) ∧
    match res.1 with
    | .ok (none, _) => ∀ l ∈ srcs, l = []
    | .ok (some v, _) => (∃ l ∈ srcs, l.head? = some v) ∧
        ∀ l ∈ srcs, ∀ x ∈ l.head?, (if rev then r (kOf κ v) (kOf κ x) else r (kOf κ x) (kOf κ v)) = false
    | .error _ => False

/-- What `mergeYieldTop h ents` returns. -/
def ytop (h : List Nat) (ents : List (MEnt α MO)) : Option α × MSt α MO :=
  if h.length > 1 then (some (ents.getD (Accel.at! h 0) default).value, .top h ents)
  else match h with
    | i :: _ => (some (ents.getD i default).value, .last (ents.getD i default))
    | [] => (none, .done)

theorem ytop_cases (h : List Nat) (ents : List (MEnt α MO)) :
    (h = [] ∧ ytop h ents = (none, .done)) ∨
      (∃ st, h ≠ [] ∧ ytop h ents = (some (ents.getD (Accel.at! h 0) default).value, st)) := by
  unfold ytop
  split
  · rename_i hl
    exact Or.inr ⟨_, by intro e; rw [e] at hl; simp at hl, rfl⟩
  · cases h with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons s t => exact Or.inr ⟨_, by simp, rfl⟩

theorem mergeYieldTop_run {W : Type} (h : List Nat) (ents : List (MEnt α MO)) (w : W) :
    (mergeYieldTop h ents : Eff W PyExc (Option α × MSt α MO)).run w = (.ok (ytop h ents), w) := by
  unfold mergeYieldTop ytop
  split
  · rfl
  · cases h <;> rfl

theorem mem_entries (srcs : List (List α)) (κ : Option (α → α)) (dir : Int) (e : MEnt α MO)
    (he : e ∈ (List.range srcs.length).filterMap (entFor srcs κ dir)) :
    (∃ l ∈ srcs, l.head? = some e.value) ∧ e.kv = kOf κ e.value := by
  simp only [List.mem_filterMap, List.mem_range, entFor] at he
  obtain ⟨i, hi, he⟩ := he
  cases hh : (srcs.getD i []).head? with
  | none => rw [hh] at he; cases he
  | some x =>
    rw [hh] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    refine ⟨⟨srcs.getD i [], ?_, hh⟩, rfl⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem head_entry (srcs : List (List α)) (κ : Option (α → α)) (dir : Int) (l : List α) (hl : l ∈ srcs)
    (x : α) (hx : l.head? = some x) :
    ∃ e ∈ (List.range srcs.length).filterMap (entFor srcs κ dir), e.kv = kOf κ x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  refine ⟨⟨kOf κ x, (i : Int) * dir, x, .it i⟩, ?_, rfl⟩
  simp only [List.mem_filterMap, List.mem_range, entFor]
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hx]

theorem mergeFirstNext_proven : MergeFirstNext := by
  intro α _ _ srcs r κ impl rev hr
  let dir : Int := if rev then -1 else 1
  let E0 := (List.range srcs.length).filterMap (entFor srcs κ dir)
  let f := entLtP r κ.isSome
  let g : Nat → Nat → Bool := fun i j => f (E0.getD i default) (E0.getD j default)
  let H := Accel.pyHeapify (heapOrd rev g) (List.range E0.length)
  have hinit := mergeInit_mEnv srcs r κ dir (List.range srcs.length) [] (srcs.map (fun _ => 0))
    (fun i _ => by simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases srcs[i]? <;> rfl)
    List.nodup_range
  rw [foldl_set_range] at hinit
  simp only [List.nil_append] at hinit
  have hcmp : entLtI (mEnv srcs r) (κ.map (pureKeyG (W := List Nat))).isSome E0 =
      fun i j => pure (g i j) := by
    funext i j; simp only [entLtI]; rw [entLt_mEnv srcs r hr]; cases κ <;> rfl
  have hbody : (mergeBody (mEnv srcs r) impl (κ.map pureKeyG) rev ((List.range srcs.length).map MO.src)
      .start).run (srcs.map (fun _ => 0)) = (.ok (ytop H E0), srcs.map (fun l => min 1 l.length)) := by
    simp only [mergeBody]
    rw [zipIdx_map_src, Eff.run_bind_ok hinit, hcmp, Eff.run_bind_ok (hHeapify_pure impl rev g _ _),
      reraise_ok, Eff.pure_bind]
    exact mergeYieldTop_run H E0 _
  have hstep : (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev ((List.range srcs.length).map MO.src)
      .start).run (srcs.map (fun _ => 0)) = (.ok (ytop H E0), srcs.map (fun l => min 1 l.length)) := by
    simp only [mergeStep, Eff.run_bind, Eff.attempt, hbody]
    rfl
  simp only [hstep, true_and]
  have hsw := strictWeak_heapOrd (StrictWeak.pullback (strictWeak_entLtP hr κ.isSome)
    (fun i => E0.getD i default)) rev
  obtain ⟨hheap, hperm⟩ := Accel.pyHeapify_correct hsw (List.range E0.length)
  have hmin := Accel.root_min_mem hsw H hheap
  have hgetD : ∀ j (hj : j < E0.length), E0.getD j default = E0[j]'hj := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  -- the root refers to an entry of a head, smallest among the heads
  have hroot : ∀ s, Accel.at! H 0 = s → s ∈ H →
      (∃ l ∈ srcs, l.head? = some (E0.getD s default).value) ∧
        ∀ l ∈ srcs, ∀ x ∈ l.head?, (if rev then r (kOf κ (E0.getD s default).value) (kOf κ x)
          else r (kOf κ x) (kOf κ (E0.getD s default).value)) = false := by
    intro s hs hsH
    have hsl : s < E0.length := by simpa using hperm.mem_iff.1 hsH
    obtain ⟨hs1, hs2⟩ := mem_entries srcs κ dir (E0.getD s default) (by rw [hgetD s hsl]; exact List.getElem_mem hsl)
    refine ⟨hs1, fun l hl x hx => ?_⟩
    obtain ⟨e, heE, hek⟩ := head_entry srcs κ dir l hl x hx
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem heE
    have := hmin j (hperm.mem_iff.2 (by simpa using hj))
    rw [hs] at this
    cases rev
    · simp only [heapOrd, Bool.false_eq_true, if_false, entLtP, lexLt, Bool.or_eq_false_iff] at this
      rw [hgetD j hj, hje] at this
      simp only [Bool.false_eq_true, if_false]
      rw [← hek, ← hs2]; exact this.1
    · simp only [heapOrd, if_true, Accel.maxLt, entLtP, lexLt, Bool.or_eq_false_iff] at this
      rw [hgetD j hj, hje] at this
      simp only [if_true]
      rw [← hek, ← hs2]; exact this.1
  rcases ytop_cases H E0 with ⟨hH0, hy⟩ | ⟨st, hne, hy⟩
  · rw [hy]
    intro l hl
    cases hx : l.head? with
    | none => exact List.head?_eq_none_iff.1 hx
    | some x =>
      obtain ⟨e, heE, _⟩ := head_entry srcs κ dir l hl x hx
      obtain ⟨j, hj, _⟩ := List.getElem_of_mem heE
      have : j ∈ H := hperm.mem_iff.2 (by simpa using hj)
      rw [hH0] at this
      simp at this
  · rw [hy]
    have hmem : Accel.at! H 0 ∈ H := by
      obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
      rw [hys]; simp [Accel.at!]
    exact hroot _ rfl hmem

/-- **`merge` never loses items silently**: with honest inputs and comparisons, whatever the
(fallible) key does, `list(merge(*inputs, key=key))` either raises or returns every item of the
inputs. Refuted: a key raising `StopIteration` is caught by the `except StopIteration` meant
for exhausted inputs (Lib/heapq.py:391, :403), so the input is dropped. -/
def MergeNoSilentDrop : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (srcs : List (List α)) (r : α → α → Bool)
    (key : α → Eff (List Nat) PyExc α) (impl rev : Bool) (fuel : Nat) (out : List α) (w' : List Nat),
    Accel.StrictWeak r →
    (mergeDrain (mEnv srcs r) impl (some key) rev ((List.range srcs.length).map MO.src) fuel .start).run
        (srcs.map (fun _ => 0)) = (.ok out, w') →
      out.length = (srcs.map List.length).sum

/-- A key that raises `StopIteration` for `5` and is the identity otherwise. -/
def stopAt5 : Int → Eff (List Nat) PyExc Int := fun x =>
  if x = 5 then Eff.raise .stopIteration else pure x

/-- `list(merge([1, 5], [2], key=key))` with `key(5)` raising `StopIteration` returns `[1, 2]`. -/
theorem mergeNoSilentDrop_refuted : ¬ MergeNoSilentDrop := by
  intro h
  have hrun : (mergeDrain (mEnv [[1, 5], [2]] intLtB) false (some stopAt5) false
      ((List.range 2).map MO.src) 10 .start).run ([[1, 5], [2]].map (fun _ => 0)) =
      (.ok [1, 2], [2, 1]) := by decide +kernel
  have := h Int [[1, 5], [2]] intLtB stopAt5 false false 10 [1, 2] [2, 1] strictWeak_intLtB hrun
  revert this
  decide

/-- **`merge` is the stable sort of the chained inputs.** For inputs each sorted by the key
(descending for `reverse=True`), `list(merge(*inputs, key=key, reverse=reverse)) ==
sorted(chain(*inputs), key=key, reverse=reverse)`, ties included, for a strict weak order with
`==` its equivalence and a pure key. Source: the docstring (Lib/heapq.py:331-345). Stated over
the generator model; not yet proven (see the registry note). -/
def MergeIsSorted : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (srcs : List (List α)) (r : α → α → Bool)
    (κ : Option (α → α)) (impl rev : Bool) (fuel : Nat), Accel.StrictWeak r →
    (srcs.map List.length).sum + 2 < fuel →
    (∀ l ∈ srcs, l.Pairwise (fun a b => if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))) →
    ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev ((List.range srcs.length).map MO.src) fuel .start).run
        (srcs.map (fun _ => 0))).1 =
      .ok (srcs.flatten.mergeSort (fun a b => if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a)))

end PyLean.Accel.Heapq
