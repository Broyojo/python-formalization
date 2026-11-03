import PyLean.Accel.HeapqMergeBase
import PyLean.Accel.MergeProps

/-!
`list(merge(*inputs, key=key, reverse=reverse))` is the stable sort of the chained inputs, over
the generator model, for honest inputs (`mEnv`): a strict weak order with `==` its equivalence
and a pure key.

The invariant `MInv` relates a suspended generator (`.top h ents` right after a `yield`, with the
world `w` of iterator positions) to the inputs' remaining items `rs` (the current head of each
input first): every input's iterator is past its head, the heap's entries are one per non-empty
`rs[i]`, and they form a heap. Keys are read through their rank in the finite universe of keys,
which turns the strict weak order into an int key (`kfR`).
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {α : Type} [DecidableEq α] [Inhabited α]

section

variable (srcs : List (List α)) (r : α → α → Bool) (κ : Option (α → α)) (impl rev : Bool)

def mdir : Int := if rev then -1 else 1

def entN (i : Nat) (x : α) : MEnt α MO := ⟨kOf κ x, (i : Int) * mdir rev, x, .it i⟩

/-- The heap entries for the remaining items `rs`: one per non-empty input. -/
def mEntsN (rs : List (List α)) : List (MEnt α MO) :=
  (List.range srcs.length).filterMap (fun i => (rs.getD i []).head?.map (entN κ rev i))

def KUm : List α := srcs.flatten.map (kOf κ)

/-- The sort key: the rank of the key among all keys (negated for `reverse`). -/
def kfR (x : α) : Int :=
  if rev then -(rank r (KUm srcs κ) (kOf κ x) : Int) else (rank r (KUm srcs κ) (kOf κ x) : Int)

def phiE (ents : List (MEnt α MO)) (i : Nat) : MEnt α MO := ents.getD i default

def mits : List MO := (List.range srcs.length).map MO.src

structure MInv (h : List Nat) (ents : List (MEnt α MO)) (w : List Nat) (rs : List (List α)) : Prop where
  rsl : rs.length = srcs.length
  wl : w.length = srcs.length
  pos : ∀ i < srcs.length, (srcs.getD i []).drop (w.getD i 0) = (rs.getD i []).tail
  mem : ∀ i < srcs.length, ∀ x ∈ rs.getD i [], x ∈ srcs.getD i []
  sorted : ∀ i < srcs.length, (rs.getD i []).Pairwise (fun a b => kfR srcs r κ rev a ≤ kfR srcs r κ rev b)
  range : ∀ id ∈ h, id < ents.length
  perm : (h.map (phiE ents)).Perm (mEntsN srcs κ rev rs)
  heap : Accel.IsHeap (heapOrd rev (entLtP r κ.isSome)) (h.map (phiE ents))

/-- What remains to be produced after the generator yielded `ytop h ents`. -/
def yRun (fuel : Nat) (h : List Nat) (ents : List (MEnt α MO)) : Eff (List Nat) PyExc (List α) :=
  match ytop h ents with
  | (none, _) => pure []
  | (some v, st) => do
    let rest ← mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) fuel st
    pure (v :: rest)

theorem drain_step (fuel : Nat) (st : MSt α MO) (h : List Nat) (ents : List (MEnt α MO)) (w w' : List Nat)
    (hs : (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) st).run w = (.ok (ytop h ents), w')) :
    (mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (fuel + 1) st).run w =
      (yRun srcs r κ impl rev fuel h ents).run w' := by
  simp only [mergeDrain]
  rw [Eff.run_bind_ok hs]
  simp only [yRun]
  rcases ytop h ents with ⟨v, st'⟩
  cases v <;> rfl

end

/-! ### Entries -/

theorem mem_mEntsN (srcs : List (List α)) (κ : Option (α → α)) (rev : Bool) (rs : List (List α))
    (e : MEnt α MO) :
    e ∈ mEntsN srcs κ rev rs ↔ ∃ i < srcs.length, ∃ x t, rs.getD i [] = x :: t ∧ e = entN κ rev i x := by
  simp only [mEntsN, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    cases hh : rs.getD i [] with
    | nil => rw [hh] at he; cases he
    | cons x t => rw [hh] at he; simp only [List.head?_cons, Option.map_some, Option.some.injEq] at he;
                  exact ⟨i, hi, x, t, hh, he.symm⟩
  · rintro ⟨i, hi, x, t, hh, rfl⟩
    exact ⟨i, hi, by rw [hh]; rfl⟩

theorem mdir_ne (rev : Bool) (i j : Nat) (h : (i : Int) * mdir rev = (j : Int) * mdir rev) : i = j := by
  cases rev <;> simp [mdir] at h <;> omega

theorem mEntsN_nodup (srcs : List (List α)) (κ : Option (α → α)) (rev : Bool) (rs : List (List α)) :
    (mEntsN srcs κ rev rs).Nodup := by
  apply List.Pairwise.filterMap (R := fun a b : Nat => a ≠ b) _ _ List.nodup_range
  intro i j hij e hi e' hj heq
  apply hij
  cases hhi : (rs.getD i []).head? with
  | none => rw [hhi] at hi; cases hi
  | some x =>
    cases hhj : (rs.getD j []).head? with
    | none => rw [hhj] at hj; cases hj
    | some y =>
      rw [hhi] at hi; rw [hhj] at hj
      simp only [Option.map_some, Option.some.injEq] at hi hj
      subst hi hj
      exact mdir_ne rev i j (congrArg MEnt.order heq)

/-! ### One `next()` under the honest callbacks -/

theorem Eff.run_bind_fst {W ε β γ : Type} {x : Eff W ε β} {f : β → Eff W ε γ} {w : W} {a : β}
    (h : (x.run w).1 = .ok a) : ((x >>= f).run w).1 = ((f a).run (x.run w).2).1 := by
  rcases hx : x.run w with ⟨r, w'⟩
  rw [hx] at h
  simp only at h
  subst h
  rw [Eff.run_bind_ok hx]

theorem drop_succ_of {l t : List α} {p : Nat} {v : α} (hd : l.drop p = v :: t) : l.drop (p + 1) = t := by
  have h2 : (l.drop p).drop 1 = t := by rw [hd]; rfl
  simpa [List.drop_drop, Nat.add_comm] using h2

theorem getD_set_self (w : List Nat) (i : Nat) (v : Nat) (hi : i < w.length) : (w.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi]

theorem getD_set_ne (w : List Nat) (i j : Nat) (v : Nat) (h : i ≠ j) : (w.set i v).getD j 0 = w.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

section steps

variable (srcs : List (List α)) (r : α → α → Bool) (κ : Option (α → α)) (impl rev : Bool)
  (hr : Accel.StrictWeak r)

include hr in
theorem entLtI_mEnv (keyed : Bool) (ents : List (MEnt α MO)) :
    entLtI (mEnv srcs r) keyed ents = fun i j => pure (entLtP r keyed (phiE ents i) (phiE ents j)) := by
  funext i j; simp only [entLtI, phiE]; rw [entLt_mEnv srcs r hr]

theorem next_mEnv_some (i : Nat) (w : List Nat) (v : α) (t : List α)
    (hd : (srcs.getD i []).drop (w.getD i 0) = v :: t) :
    ((mEnv srcs r).next (.it i)).run w = (.ok v, w.set i (w.getD i 0 + 1)) := by
  have : (srcs.getD i [])[w.getD i 0]? = some v := by
    rw [← List.head?_drop, hd]; rfl
  show (match (srcs.getD i [])[w.getD i 0]? with
    | some x => ((Except.ok x : Except PyExc α), w.set i (w.getD i 0 + 1))
    | none => (Except.error PyExc.stopIteration, w)) = _
  rw [this]

theorem next_mEnv_none (i : Nat) (w : List Nat) (hd : (srcs.getD i []).drop (w.getD i 0) = []) :
    ((mEnv srcs r).next (.it i)).run w = (.error .stopIteration, w) := by
  have : (srcs.getD i [])[w.getD i 0]? = none := by
    rw [← List.head?_drop, hd]; rfl
  show (match (srcs.getD i [])[w.getD i 0]? with
    | some x => ((Except.ok x : Except PyExc α), w.set i (w.getD i 0 + 1))
    | none => (Except.error PyExc.stopIteration, w)) = _
  rw [this]

theorem pyHeappop_ok {β : Type} [Inhabited β] (lt : β → β → Bool) (l : List β) (hne : l ≠ []) :
    ∃ v l', Accel.pyHeappop lt l = .ok (v, l') := by
  obtain ⟨d, last, rfl⟩ : ∃ d last, l = d ++ [last] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  simp only [Accel.pyHeappop, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat]
  split <;> exact ⟨_, _, rfl⟩

theorem mergeStep_ok_of_body {st : MSt α MO} {w w' : List Nat} {p : Option α × MSt α MO}
    (hb : (mergeBody (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) st).run w = (.ok p, w')) :
    (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) st).run w = (.ok p, w') := by
  simp only [mergeStep, Eff.run_bind, Eff.attempt, hb]
  rfl

include hr in
/-- The root's input has a next item: fetch it, update the root entry in place, heapreplace. -/
theorem top_step_some (h : List Nat) (ents : List (MEnt α MO)) (w : List Nat) (i : Nat) (x v : α)
    (t : List α) (hne : h ≠ []) (hsid : Accel.at! h 0 < ents.length)
    (hroot : ents.getD (Accel.at! h 0) default = entN κ rev i x)
    (hd : (srcs.getD i []).drop (w.getD i 0) = v :: t) :
    (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (.top h ents)).run w =
      (.ok (ytop (Accel.pySiftup (heapOrd rev (fun a b => entLtP r κ.isSome
          (phiE (ents.set (Accel.at! h 0) (entN κ rev i v)) a) (phiE (ents.set (Accel.at! h 0) (entN κ rev i v)) b))) h 0)
        (ents.set (Accel.at! h 0) (entN κ rev i v))), w.set i (w.getD i 0 + 1)) := by
  apply mergeStep_ok_of_body
  simp only [mergeBody]
  rw [hroot]
  have hatt : (Eff.attempt (do
        let value ← (mEnv srcs r).next (entN κ rev i x).nxt
        let kv ← applyK (Option.map pureKeyG κ) value
        pure ({ kv := kv, order := (entN κ rev i x).order, value := value, nxt := (entN κ rev i x).nxt } :
          MEnt α MO))).run w = (.ok (.ok (entN κ rev i v)), w.set i (w.getD i 0 + 1)) := by
    simp only [Eff.attempt]
    rw [Eff.run_bind_ok (show ((mEnv srcs r).next (entN κ rev i x).nxt).run w = _ from
        next_mEnv_some srcs r i w v t hd),
      Eff.run_bind_ok (show (applyK (κ.map pureKeyG) v).run (w.set i (w.getD i 0 + 1)) =
        (.ok (kOf κ v), w.set i (w.getD i 0 + 1)) by rw [applyK_pureKeyG]; rfl)]
    rfl
  rw [Eff.run_bind_ok hatt]
  dsimp only
  rw [Option.isSome_map, entLtI_mEnv srcs r hr, Eff.run_bind_ok (hHeapreplace_pure impl rev _ h _ _ hne)]
  dsimp only
  rw [Accel.set_at!_self]
  exact mergeYieldTop_run _ _ _

include hr in
/-- The root's input is exhausted: `StopIteration`, heappop. -/
theorem top_step_none (h : List Nat) (ents : List (MEnt α MO)) (w : List Nat) (i : Nat) (x : α)
    (hne : h ≠ []) (hroot : ents.getD (Accel.at! h 0) default = entN κ rev i x)
    (hd : (srcs.getD i []).drop (w.getD i 0) = []) (v0 : Nat) (h' : List Nat)
    (hpop : Accel.pyHeappop (heapOrd rev (fun a b => entLtP r κ.isSome (phiE ents a) (phiE ents b))) h = .ok (v0, h')) :
    (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (.top h ents)).run w =
      (.ok (ytop h' ents), w) := by
  apply mergeStep_ok_of_body
  simp only [mergeBody]
  rw [hroot]
  have hatt : (Eff.attempt (do
        let value ← (mEnv srcs r).next (entN κ rev i x).nxt
        let kv ← applyK (Option.map pureKeyG κ) value
        pure ({ kv := kv, order := (entN κ rev i x).order, value := value, nxt := (entN κ rev i x).nxt } :
          MEnt α MO))).run w = (.ok (.error .stopIteration), w) := by
    simp only [Eff.attempt]
    rw [Eff.run_bind_err (show ((mEnv srcs r).next (entN κ rev i x).nxt).run w = _ from
        next_mEnv_none srcs r i w hd)]
  rw [Eff.run_bind_ok hatt]
  dsimp only
  rw [if_pos (show isA (mEnv srcs r).hier .stopIteration "StopIteration" = true from isA_stop),
    Option.isSome_map, entLtI_mEnv srcs r hr, Eff.run_bind_ok (hHeappop_pure impl rev _ h w v0 h' hpop), reraise_ok,
    Eff.pure_bind]
  exact mergeYieldTop_run _ _ _

theorem yfrom_drain (i : Nat) :
    ∀ (fuel : Nat) (w : List Nat) (t : List α), i < w.length →
      (srcs.getD i []).drop (w.getD i 0) = t → t.length < fuel →
      ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) fuel (.yfrom (.it i))).run w).1 = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro w t hi hd hf
    simp only [mergeDrain]
    cases t with
    | nil =>
      have hs : (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (.yfrom (.it i))).run w =
          (.ok (none, .done), w) := by
        apply mergeStep_ok_of_body
        simp only [mergeBody, mergeYieldFrom]
        rw [Eff.run_bind_ok (nextOpt_stop _ _ _ _ _ (next_mEnv_none srcs r i w hd) isA_stop)]
        rfl
      rw [Eff.run_bind_ok hs]; rfl
    | cons v t =>
      have hs : (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (.yfrom (.it i))).run w =
          (.ok (some v, .yfrom (.it i)), w.set i (w.getD i 0 + 1)) := by
        apply mergeStep_ok_of_body
        simp only [mergeBody, mergeYieldFrom]
        rw [Eff.run_bind_ok (nextOpt_ok _ _ _ _ _ (next_mEnv_some srcs r i w v t hd))]
        rfl
      rw [Eff.run_bind_ok hs]
      simp only
      have hd' : (srcs.getD i []).drop ((w.set i (w.getD i 0 + 1)).getD i 0) = t := by
        rw [getD_set_self w i _ hi]; exact drop_succ_of hd
      rw [Eff.run_bind_fst (ih _ t (by simp; exact hi) hd' (by simp at hf; omega))]
      rfl

end steps

/-! ### List facts -/

theorem filterMap_extract {β : Type} (L : List Nat) (hL : L.Nodup) (i : Nat) (hi : i ∈ L) (f : Nat → Option β) :
    (L.filterMap f).Perm ((f i).toList ++ (L.erase i).filterMap f) := by
  have hp := (List.perm_cons_erase hi).filterMap f
  refine hp.trans ?_
  simp only [List.filterMap_cons]
  cases f i <;> simp

theorem filterMap_congr' {β : Type} (f g : Nat → Option β) :
    ∀ (L : List Nat), (∀ j ∈ L, f j = g j) → L.filterMap f = L.filterMap g
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.filterMap_cons, h a (by simp), filterMap_congr' f g L (fun j hj => h j (by simp [hj]))]

theorem filterMap_erase_congr {β : Type} (L : List Nat) (hL : L.Nodup) (i : Nat) (f g : Nat → Option β)
    (hfg : ∀ j, j ≠ i → f j = g j) : (L.erase i).filterMap f = (L.erase i).filterMap g := by
  apply filterMap_congr'
  intro j hj
  apply hfg
  intro hji; subst hji
  exact (List.Nodup.not_mem_erase hL) hj

theorem flatten_split (rs : List (List α)) (i : Nat) (hi : i < rs.length) :
    rs.flatten = (rs.take i).flatten ++ rs.getD i [] ++ (rs.drop (i + 1)).flatten := by
  have hg : rs.getD i [] = rs[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hg, List.append_assoc, ← List.flatten_cons, ← List.drop_eq_getElem_cons hi, ← List.flatten_append,
    List.take_append_drop]

theorem pyHeappop_perm {β : Type} [Inhabited β] (lt : β → β → Bool) (l : List β) (v : β) (l' : List β)
    (h : Accel.pyHeappop lt l = .ok (v, l')) : (v :: l').Perm l := by
  cases hl : l with
  | nil => rw [hl] at h; cases h
  | cons y ys =>
    obtain ⟨d, last, hdl⟩ : ∃ d last, y :: ys = d ++ [last] :=
      ⟨(y :: ys).dropLast, (y :: ys).getLast (by simp), (List.dropLast_concat_getLast (by simp)).symm⟩
    rw [hl, hdl] at h
    rw [hdl]
    simp only [Accel.pyHeappop, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_concat] at h
    cases d with
    | nil => simp at h; obtain ⟨rfl, rfl⟩ := h; simp
    | cons d0 dt =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp := pySiftup_perm lt ((d0 :: dt).set 0 last) 0 (by simp)
      have : (d0 :: dt).set 0 last = last :: dt := rfl
      rw [this] at hp
      have h0 : Accel.at! (d0 :: dt) 0 = d0 := rfl
      rw [h0]
      exact (List.Perm.cons d0 hp).trans (List.Perm.cons d0 (List.perm_append_comm (l₁ := [last]) (l₂ := dt)))

theorem pyHeapify_perm {β : Type} [Inhabited β] (lt : β → β → Bool) (l : List β) :
    (Accel.pyHeapify lt l).Perm l := by
  simp only [Accel.pyHeapify]
  have : ∀ (is : List Nat) (m : List β), m.length = l.length → (∀ i ∈ is, i < l.length) →
      (is.foldl (fun h i => Accel.pySiftup lt h i) m).Perm m := by
    intro is
    induction is with
    | nil => intro m _ _; exact List.Perm.refl _
    | cons i is ih =>
      intro m hm hi
      simp only [List.foldl_cons]
      have h1 := pySiftup_perm lt m i (by rw [hm]; exact hi i (by simp))
      exact (ih _ (by rw [Accel.pySiftup_length, hm]) (fun j hj => hi j (by simp [hj]))).trans h1
  exact this _ l rfl (fun i hi => by simp at hi; omega)

theorem map_set_nodup {β : Type} [Inhabited β] (h : List Nat) (ents : List β) (sid : Nat) (b : β)
    (hnd : h.Nodup) (h0 : Accel.at! h 0 = sid) (hne : h ≠ []) (hsid : sid < ents.length) :
    h.map (fun j => (ents.set sid b).getD j default) = (h.map (fun j => ents.getD j default)).set 0 b := by
  cases h with
  | nil => exact absurd rfl hne
  | cons y ys =>
    have hy : y = sid := h0
    subst hy
    simp only [List.map_cons, List.set_cons_zero]
    congr 1
    · simp [List.getD_eq_getElem?_getD, hsid]
    · apply List.map_congr_left
      intro j hj
      have hne : y ≠ j := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hj)
      simp [List.getD_eq_getElem?_getD, hne]

theorem getD_set_eq' {β : Type} (l : List β) (i : Nat) (v d : β) (hi : i < l.length) :
    (l.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi]

theorem getD_set_ne' {β : Type} (l : List β) (i j : Nat) (v d : β) (h : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem take_set_self {β : Type} (l : List β) (i : Nat) (a : β) : (l.set i a).take i = l.take i := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_take, List.getElem_set]
  rw [if_neg]
  simp at h1; omega

theorem drop_set_self {β : Type} (l : List β) (i : Nat) (a : β) :
    (l.set i a).drop (i + 1) = l.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_drop, List.getElem_set]
  rw [if_neg]
  omega

theorem flatten_set (rs : List (List α)) (i : Nat) (hi : i < rs.length) (l : List α) :
    (rs.set i l).flatten = (rs.take i).flatten ++ l ++ (rs.drop (i + 1)).flatten := by
  rw [flatten_split (rs.set i l) i (by simpa using hi), getD_set_eq' rs i l [] hi, take_set_self, drop_set_self]

theorem flatten_len (rs : List (List α)) (i : Nat) (hi : i < rs.length) (x : α) (t : List α)
    (hrs : rs.getD i [] = x :: t) : (rs.set i t).flatten.length + 1 = rs.flatten.length := by
  rw [flatten_set rs i hi t, flatten_split rs i hi, hrs]
  simp only [List.length_append, List.length_cons]
  omega

theorem mem_take_flatten (rs : List (List α)) (i : Nat) (y : α) (hy : y ∈ (rs.take i).flatten) :
    ∃ j < i, j < rs.length ∧ y ∈ rs.getD j [] := by
  obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.length_take] at hk
  refine ⟨k, by omega, by omega, ?_⟩
  rw [List.getElem_take] at hyl
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < rs.length by omega)] using hyl

theorem mem_drop_flatten (rs : List (List α)) (i : Nat) (y : α) (hy : y ∈ (rs.drop (i + 1)).flatten) :
    ∃ j, i < j ∧ j < rs.length ∧ y ∈ rs.getD j [] := by
  obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.length_drop] at hk
  refine ⟨i + 1 + k, by omega, by omega, ?_⟩
  rw [List.getElem_drop] at hyl
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i + 1 + k < rs.length by omega)] using hyl

theorem flatten_nil_of (rs : List (List α)) (h : ∀ i < rs.length, rs.getD i [] = []) : rs.flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  have := h k hk
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this

theorem getD_mem_of {β : Type} (l : List (List β)) (i : Nat) (hi : i < l.length) : l.getD i [] ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem range_map_getD {β : Type} [Inhabited β] (l : List β) :
    (List.range l.length).map (fun i => l.getD i default) = l := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem at!_mem0 {β : Type} [Inhabited β] (h : List β) (hne : h ≠ []) : Accel.at! h 0 ∈ h := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [Accel.at!]

theorem heapOrd_comp {β γ : Type} (rev : Bool) (F : γ → γ → Bool) (φ : β → γ) :
    heapOrd rev (fun a b => F (φ a) (φ b)) = fun a b => heapOrd rev F (φ a) (φ b) := by
  cases rev <;> rfl

theorem kum_mem (srcs : List (List α)) (κ : Option (α → α)) (i : Nat) (hi : i < srcs.length) (x : α)
    (hx : x ∈ srcs.getD i []) : kOf κ x ∈ KUm srcs κ :=
  List.mem_map.2 ⟨x, List.mem_flatten.2 ⟨_, getD_mem_of srcs i hi, hx⟩, rfl⟩

/-! ### The invariant across one `next()` -/

section main

variable (srcs : List (List α)) (r : α → α → Bool) (κ : Option (α → α)) (impl rev : Bool)
  (hr : Accel.StrictWeak r)

theorem mEntsN_split (rs : List (List α)) (i : Nat) (hi : i < srcs.length) :
    (mEntsN srcs κ rev rs).Perm (((rs.getD i []).head?.map (entN κ rev i)).toList ++
      ((List.range srcs.length).erase i).filterMap (fun j => (rs.getD j []).head?.map (entN κ rev j))) :=
  filterMap_extract _ List.nodup_range i (List.mem_range.2 hi) _

theorem mEntsN_set_rest (rs : List (List α)) (i : Nat) (l : List α) :
    ((List.range srcs.length).erase i).filterMap (fun j => ((rs.set i l).getD j []).head?.map (entN κ rev j)) =
      ((List.range srcs.length).erase i).filterMap (fun j => (rs.getD j []).head?.map (entN κ rev j)) :=
  filterMap_erase_congr _ List.nodup_range i _ _ (fun j hj => by rw [getD_set_ne' rs i j l [] (Ne.symm hj)])

include hr in
/-- The heap order on two entries, read as sort keys: the root `entN i x` is not above
`entN j y`. -/
theorem ho_false (i j : Nat) (x y : α) (hij : i ≠ j) (hx : kOf κ x ∈ KUm srcs κ) (hy : kOf κ y ∈ KUm srcs κ)
    (h : heapOrd rev (entLtP r κ.isSome) (entN κ rev j y) (entN κ rev i x) = false) :
    kfR srcs r κ rev x < kfR srcs r κ rev y ∨ (kfR srcs r κ rev x = kfR srcs r κ rev y ∧ i < j) := by
  have h1 := rank_spec hr (KUm srcs κ) hx hy
  have h2 := rank_spec hr (KUm srcs κ) hy hx
  cases rev
  · simp only [heapOrd, Bool.false_eq_true, if_false, entLtP, entN, lexLt, h1, h2, intLtB, mdir] at h
    simp only [kfR, Bool.false_eq_true, if_false]
    by_cases hab : rank r (KUm srcs κ) (kOf κ x) < rank r (KUm srcs κ) (kOf κ y)
    · left; omega
    · by_cases hba : rank r (KUm srcs κ) (kOf κ y) < rank r (KUm srcs κ) (kOf κ x)
      · simp [hba] at h
      · right
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
        · exact hlt
        · simp [hab, hba, show (j : Int) < i by omega] at h
  · simp only [heapOrd, if_true, Accel.maxLt, entLtP, entN, lexLt, h1, h2, intLtB, mdir] at h
    simp only [kfR, if_true]
    by_cases hab : rank r (KUm srcs κ) (kOf κ y) < rank r (KUm srcs κ) (kOf κ x)
    · left; omega
    · by_cases hba : rank r (KUm srcs κ) (kOf κ x) < rank r (KUm srcs κ) (kOf κ y)
      · simp [hba] at h
      · right
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
        · exact hlt
        · simp [hab, hba, show -(i : Int) < -(j : Int) by omega] at h

theorem root_entry {h : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev h ents w rs) (hne : h ≠ []) :
    ∃ i < srcs.length, ∃ x t, rs.getD i [] = x :: t ∧ phiE ents (Accel.at! h 0) = entN κ rev i x := by
  have hm : phiE ents (Accel.at! h 0) ∈ h.map (phiE ents) := List.mem_map.2 ⟨_, at!_mem0 h hne, rfl⟩
  exact (mem_mEntsN srcs κ rev rs _).1 (hI.perm.mem_iff.1 hm)

theorem h_nodup {h : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev h ents w rs) : h.Nodup := by
  have := hI.perm.nodup_iff.2 (mEntsN_nodup srcs κ rev rs)
  exact (List.pairwise_map.1 this).imp (fun hab e => hab (congrArg (phiE ents) e))

include hr in
/-- Every remaining item is at or above the root's key, and strictly above it in the inputs
before the root's. -/
theorem heads_bound {h : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev h ents w rs) (hne : h ≠ []) (i : Nat) (hi : i < srcs.length) (x : α) (t : List α)
    (hrs : rs.getD i [] = x :: t) (hroot : phiE ents (Accel.at! h 0) = entN κ rev i x)
    (j : Nat) (hj : j < srcs.length) (hji : j ≠ i) (y : α) (hy : y ∈ rs.getD j []) :
    kfR srcs r κ rev x ≤ kfR srcs r κ rev y ∧ (j < i → kfR srcs r κ rev x < kfR srcs r κ rev y) := by
  obtain ⟨hd, tl, hht⟩ : ∃ hd tl, rs.getD j [] = hd :: tl := by
    cases hh : rs.getD j [] with
    | nil => rw [hh] at hy; cases hy
    | cons a b => exact ⟨a, b, rfl⟩
  have hsorted := hI.sorted j hj
  rw [hht] at hsorted
  have hle : kfR srcs r κ rev hd ≤ kfR srcs r κ rev y := by
    rw [hht] at hy
    rcases List.mem_cons.1 hy with e | e
    · rw [e]; exact Int.le_refl _
    · exact (List.pairwise_cons.1 hsorted).1 y e
  have hmem : entN κ rev j hd ∈ h.map (phiE ents) :=
    hI.perm.mem_iff.2 ((mem_mEntsN srcs κ rev rs _).2 ⟨j, hj, hd, tl, hht, rfl⟩)
  have hsw := strictWeak_heapOrd (strictWeak_entLtP hr κ.isSome) rev
  have hmin := Accel.root_min_mem hsw _ hI.heap _ hmem
  rw [at!_map_lt _ h 0 (List.length_pos_iff.2 hne), hroot] at hmin
  have hxm : x ∈ srcs.getD i [] := hI.mem i hi x (by rw [hrs]; exact List.mem_cons_self)
  have hdm : hd ∈ srcs.getD j [] := hI.mem j hj hd (by rw [hht]; exact List.mem_cons_self)
  rcases ho_false srcs r κ rev hr i j x hd (Ne.symm hji) (kum_mem srcs κ i hi x hxm) (kum_mem srcs κ j hj hd hdm)
      hmin with h1 | ⟨h1, h2⟩
  · exact ⟨by omega, fun _ => by omega⟩
  · exact ⟨by omega, fun h3 => by omega⟩

include hr in
/-- The root's item is the stable sort's first item. -/
theorem finish_eq {h : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev h ents w rs) (hne : h ≠ []) (i : Nat) (hi : i < srcs.length) (x : α) (t : List α)
    (hrs : rs.getD i [] = x :: t) (hroot : phiE ents (Accel.at! h 0) = entN κ rev i x) :
    gStableSort (kfR srcs r κ rev) rs.flatten = x :: gStableSort (kfR srcs r κ rev) (rs.set i t).flatten := by
  have hil : i < rs.length := by rw [hI.rsl]; exact hi
  rw [flatten_split rs i hil, flatten_set rs i hil t, hrs]
  simp only [List.append_assoc, List.cons_append]
  apply gStableSort_extract
  · intro y hy
    obtain ⟨j, hj, hjl, hyj⟩ := mem_take_flatten rs i y hy
    exact (heads_bound srcs r κ rev hr hI hne i hi x t hrs hroot j (by rw [← hI.rsl]; exact hjl) (by omega) y hyj).2 hj
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · have hs := hI.sorted i hi
      rw [hrs] at hs
      exact (List.pairwise_cons.1 hs).1 y hy
    · obtain ⟨j, hj, hjl, hyj⟩ := mem_drop_flatten rs i y hy
      exact (heads_bound srcs r κ rev hr hI hne i hi x t hrs hroot j (by rw [← hI.rsl]; exact hjl) (by omega) y hyj).1

theorem perm_core {a : Nat} {hs : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev (a :: hs) ents w rs) (i : Nat) (hi : i < srcs.length) (x : α) (t : List α)
    (hrs : rs.getD i [] = x :: t) (hroot : phiE ents (Accel.at! (a :: hs) 0) = entN κ rev i x) :
    (hs.map (phiE ents)).Perm
      (((List.range srcs.length).erase i).filterMap (fun j => (rs.getD j []).head?.map (entN κ rev j))) := by
  have h1 := hI.perm.trans (mEntsN_split srcs κ rev rs i hi)
  rw [hrs] at h1
  have hroot' : phiE ents a = entN κ rev i x := hroot
  simp only [List.map_cons, hroot', List.head?_cons, Option.map_some, Option.toList_some,
    List.singleton_append] at h1
  exact h1.cons_inv

include hr in
/-- The root's input had a next item `v`: the entry is updated in place and sifted. -/
theorem inv_some {a : Nat} {hs : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev (a :: hs) ents w rs) (i : Nat) (hi : i < srcs.length) (x v : α) (t' : List α)
    (hrs : rs.getD i [] = x :: v :: t') (hroot : phiE ents (Accel.at! (a :: hs) 0) = entN κ rev i x) :
    MInv srcs r κ rev
      (Accel.pySiftup (heapOrd rev (fun p q => entLtP r κ.isSome
          (phiE (ents.set (Accel.at! (a :: hs) 0) (entN κ rev i v)) p)
          (phiE (ents.set (Accel.at! (a :: hs) 0) (entN κ rev i v)) q))) (a :: hs) 0)
      (ents.set (Accel.at! (a :: hs) 0) (entN κ rev i v)) (w.set i (w.getD i 0 + 1)) (rs.set i (v :: t')) := by
  have hil : i < rs.length := by rw [hI.rsl]; exact hi
  have hiw : i < w.length := by rw [hI.wl]; exact hi
  have hne : (a :: hs) ≠ [] := by simp
  have ha : Accel.at! (a :: hs) 0 = a := rfl
  have hroot' : phiE ents a = entN κ rev i x := hroot
  have hsid : a < ents.length := hI.range a (by simp)
  have hnd := h_nodup srcs r κ rev hI
  have hmap2 : (a :: hs).map (phiE (ents.set a (entN κ rev i v))) = entN κ rev i v :: hs.map (phiE ents) :=
    map_set_nodup (a :: hs) ents a (entN κ rev i v) hnd rfl hne hsid
  rw [ha]
  have hsw := strictWeak_heapOrd (strictWeak_entLtP hr κ.isSome) rev
  have hmapS : (Accel.pySiftup (heapOrd rev (fun p q => entLtP r κ.isSome
        (phiE (ents.set a (entN κ rev i v)) p) (phiE (ents.set a (entN κ rev i v)) q))) (a :: hs) 0).map
        (phiE (ents.set a (entN κ rev i v))) =
      Accel.pySiftup (heapOrd rev (entLtP r κ.isSome)) (entN κ rev i v :: hs.map (phiE ents)) 0 := by
    rw [← hmap2, pySiftup_mapR (phiE (ents.set a (entN κ rev i v))) (heapOrd rev (entLtP r κ.isSome)) (a :: hs) 0
      (by simp), heapOrd_comp]
  have hold : (a :: hs).map (phiE ents) = entN κ rev i x :: hs.map (phiE ents) := by
    simp only [List.map_cons, hroot']
  obtain ⟨hheap2, hperm2⟩ := Accel.pySiftup_root hsw ((a :: hs).map (phiE ents))
    (entN κ rev i v :: hs.map (phiE ents)) hI.heap (by simp) (by simp)
    (fun k hk0 _ => by
      rw [hold]
      cases k with
      | zero => exact absurd rfl hk0
      | succ k => rfl)
  constructor
  · simp [hI.rsl]
  · simp [hI.wl]
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [getD_set_self w j _ hiw, getD_set_eq' rs j _ [] hil]
      exact drop_succ_of (by rw [hI.pos j hj, hrs]; rfl)
    · rw [getD_set_ne w i j _ (Ne.symm hji), getD_set_ne' rs i j _ [] (Ne.symm hji)]
      exact hI.pos j hj
  · intro j hj y hy
    by_cases hji : j = i
    · subst hji
      rw [getD_set_eq' rs j _ [] hil] at hy
      exact hI.mem j hj y (by rw [hrs]; exact List.mem_cons_of_mem _ hy)
    · rw [getD_set_ne' rs i j _ [] (Ne.symm hji)] at hy
      exact hI.mem j hj y hy
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [getD_set_eq' rs j _ [] hil]
      have := hI.sorted j hj
      rw [hrs] at this
      exact (List.pairwise_cons.1 this).2
    · rw [getD_set_ne' rs i j _ [] (Ne.symm hji)]
      exact hI.sorted j hj
  · intro id hid
    rw [List.length_set]
    exact hI.range id ((pySiftup_perm _ (a :: hs) 0 (by simp)).mem_iff.1 hid)
  · rw [hmapS]
    refine hperm2.trans ?_
    have hc := perm_core srcs r κ rev hI i hi x (v :: t') hrs hroot
    have h2 := mEntsN_split srcs κ rev (rs.set i (v :: t')) i hi
    rw [getD_set_eq' rs i _ [] hil, mEntsN_set_rest] at h2
    simp only [List.head?_cons, Option.map_some, Option.toList_some, List.singleton_append] at h2
    exact (List.Perm.cons _ hc).trans h2.symm
  · rw [hmapS]
    exact hheap2

include hr in
/-- The root's input was exhausted: the entry is popped. -/
theorem inv_none {a : Nat} {hs : List Nat} {ents : List (MEnt α MO)} {w : List Nat} {rs : List (List α)}
    (hI : MInv srcs r κ rev (a :: hs) ents w rs) (i : Nat) (hi : i < srcs.length) (x : α)
    (hrs : rs.getD i [] = [x]) (hroot : phiE ents (Accel.at! (a :: hs) 0) = entN κ rev i x) (v0 : Nat) (h' : List Nat)
    (hpop : Accel.pyHeappop (heapOrd rev (fun p q => entLtP r κ.isSome (phiE ents p) (phiE ents q))) (a :: hs) =
      .ok (v0, h')) :
    MInv srcs r κ rev h' ents w (rs.set i []) := by
  have hil : i < rs.length := by rw [hI.rsl]; exact hi
  have hsw := strictWeak_heapOrd (strictWeak_entLtP hr κ.isSome) rev
  have hmapP : Accel.pyHeappop (heapOrd rev (entLtP r κ.isSome)) ((a :: hs).map (phiE ents)) =
      .ok (phiE ents v0, h'.map (phiE ents)) := by
    rw [pyHeappop_mapR (phiE ents) (heapOrd rev (entLtP r κ.isSome)) (a :: hs) (by simp), ← heapOrd_comp, hpop]
    rfl
  obtain ⟨v, hh', hp, hheap', hperm', _⟩ := Accel.pyHeappop_correct hsw _ hI.heap (by simp)
  rw [hmapP] at hp
  simp only [Except.ok.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  have hv0 : v0 = a := Accel.pyHeappop_fst _ _ _ _ hpop
  constructor
  · simp [hI.rsl]
  · exact hI.wl
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [getD_set_eq' rs j _ [] hil, hI.pos j hj, hrs]
      rfl
    · rw [getD_set_ne' rs i j _ [] (Ne.symm hji)]
      exact hI.pos j hj
  · intro j hj y hy
    by_cases hji : j = i
    · subst hji
      rw [getD_set_eq' rs j _ [] hil] at hy
      cases hy
    · rw [getD_set_ne' rs i j _ [] (Ne.symm hji)] at hy
      exact hI.mem j hj y hy
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [getD_set_eq' rs j _ [] hil]
      exact List.Pairwise.nil
    · rw [getD_set_ne' rs i j _ [] (Ne.symm hji)]
      exact hI.sorted j hj
  · intro id hid
    exact hI.range id ((pyHeappop_perm _ _ _ _ hpop).mem_iff.1 (List.mem_cons_of_mem _ hid))
  · have hc := perm_core srcs r κ rev hI i hi x [] hrs hroot
    have h3 : (h'.map (phiE ents)).Perm (hs.map (phiE ents)) := by
      have := hperm'
      rw [hv0] at this
      simp only [List.map_cons] at this
      exact this.cons_inv
    have h2 := mEntsN_split srcs κ rev (rs.set i []) i hi
    rw [getD_set_eq' rs i _ [] hil, mEntsN_set_rest] at h2
    simp only [List.head?_nil, Option.map_none, Option.toList_none, List.nil_append] at h2
    exact (h3.trans hc).trans h2.symm
  · exact hheap'

/-! ### Draining the generator -/

theorem last_drain (fuel : Nat) (i : Nat) (x : α) :
    mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) fuel (.last (entN κ rev i x)) =
      mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) fuel (.yfrom (.it i)) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rfl

theorem yRun_nil (fuel : Nat) (ents : List (MEnt α MO)) (w : List Nat) (rs : List (List α))
    (hI : MInv srcs r κ rev [] ents w rs) :
    ((yRun srcs r κ impl rev fuel [] ents).run w).1 = .ok (gStableSort (kfR srcs r κ rev) rs.flatten) := by
  have hm : [] = mEntsN srcs κ rev rs := List.Perm.nil_eq hI.perm
  have hflat : rs.flatten = [] := flatten_nil_of rs (fun i hi => by
    cases hh : rs.getD i [] with
    | nil => rfl
    | cons x t =>
      exfalso
      have := (mem_mEntsN srcs κ rev rs (entN κ rev i x)).2 ⟨i, by rw [← hI.rsl]; exact hi, x, t, hh, rfl⟩
      rw [← hm] at this
      cases this)
  rw [hflat]
  simp only [gStableSort, List.mergeSort_nil]
  rfl

include hr in
/-- **The main induction**: from any suspended state satisfying the invariant, the rest of
the output is the stable sort of the remaining items. -/
theorem yRun_sorted : ∀ (fuel : Nat) (h : List Nat) (ents : List (MEnt α MO)) (w : List Nat) (rs : List (List α)),
    MInv srcs r κ rev h ents w rs → rs.flatten.length ≤ fuel →
    ((yRun srcs r κ impl rev fuel h ents).run w).1 = .ok (gStableSort (kfR srcs r κ rev) rs.flatten) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h ents w rs hI hf
    by_cases hne : h = []
    · subst hne; exact yRun_nil srcs r κ impl rev 0 ents w rs hI
    · obtain ⟨i, hi, x, t, hrs, _⟩ := root_entry srcs r κ rev hI hne
      have := flatten_len rs i (by rw [hI.rsl]; exact hi) x t hrs
      omega
  | succ fuel ih =>
    intro h ents w rs hI hf
    rcases h with _ | ⟨a, _ | ⟨b, hs⟩⟩
    · exact yRun_nil srcs r κ impl rev _ ents w rs hI
    · -- one input left: `yield from next.__self__`
      obtain ⟨i, hi, x, t, hrs, hroot⟩ := root_entry srcs r κ rev hI (by simp)
      have hil : i < rs.length := by rw [hI.rsl]; exact hi
      have hroot' : ents.getD a default = entN κ rev i x := hroot
      have hyt : ytop [a] ents = (some x, .last (entN κ rev i x)) := by
        show (if [a].length > 1 then _ else _) = _
        rw [if_neg (by simp)]
        show (some (ents.getD a default).value, MSt.last (ents.getD a default)) = _
        rw [hroot']
        rfl
      unfold yRun
      rw [hyt]
      dsimp only
      have hlen := flatten_len rs i hil x t hrs
      have hlt : t.length ≤ (rs.set i t).flatten.length := by
        rw [flatten_set rs i hil t]; simp only [List.length_append]; omega
      have hdr : ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (fuel + 1)
          (.last (entN κ rev i x))).run w).1 = .ok t := by
        rw [last_drain]
        exact yfrom_drain srcs r κ impl rev i (fuel + 1) w t (by rw [hI.wl]; exact hi)
          (by rw [hI.pos i hi, hrs]; rfl) (by omega)
      rw [Eff.run_bind_fst hdr]
      -- the other inputs are empty
      have hother : ∀ j < rs.length, j ≠ i → rs.getD j [] = [] := by
        intro j hj hji
        cases hh : rs.getD j [] with
        | nil => rfl
        | cons y u =>
          exfalso
          have hm := hI.perm.mem_iff.2 ((mem_mEntsN srcs κ rev rs (entN κ rev j y)).2
            ⟨j, by rw [← hI.rsl]; exact hj, y, u, hh, rfl⟩)
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
          have ho := congrArg MEnt.order (hm.trans hroot)
          exact hji (mdir_ne rev j i ho)
      have hA : (rs.take i).flatten = [] := List.eq_nil_iff_forall_not_mem.2 (fun y hy => by
        obtain ⟨j, hj, hjl, hyj⟩ := mem_take_flatten rs i y hy
        rw [hother j hjl (by omega)] at hyj
        cases hyj)
      have hB : (rs.drop (i + 1)).flatten = [] := List.eq_nil_iff_forall_not_mem.2 (fun y hy => by
        obtain ⟨j, hj, hjl, hyj⟩ := mem_drop_flatten rs i y hy
        rw [hother j hjl (by omega)] at hyj
        cases hyj)
      rw [flatten_split rs i hil, hA, hB, hrs, List.nil_append, List.append_nil,
        gStableSort_of_sorted _ _ (by rw [← hrs]; exact hI.sorted i hi)]
      rfl
    · -- two or more inputs left: the main loop
      have hne : (a :: b :: hs) ≠ [] := by simp
      obtain ⟨i, hi, x, t, hrs, hroot⟩ := root_entry srcs r κ rev hI hne
      have hil : i < rs.length := by rw [hI.rsl]; exact hi
      have hyt : ytop (a :: b :: hs) ents = (some x, .top (a :: b :: hs) ents) := by
        show (if (a :: b :: hs).length > 1 then _ else _) = _
        rw [if_pos (by simp)]
        show (some (phiE ents (Accel.at! (a :: b :: hs) 0)).value, _) = _
        rw [hroot]
        rfl
      unfold yRun
      rw [hyt]
      dsimp only
      have hsid : Accel.at! (a :: b :: hs) 0 < ents.length := hI.range _ (at!_mem0 _ hne)
      have hlen := flatten_len rs i hil x t hrs
      rw [finish_eq srcs r κ rev hr hI hne i hi x t hrs hroot]
      cases t with
      | cons v t' =>
        have hd : (srcs.getD i []).drop (w.getD i 0) = v :: t' := by rw [hI.pos i hi, hrs]; rfl
        have hs1 := top_step_some srcs r κ impl rev hr _ ents w i x v t' hne hsid hroot hd
        have hdr : ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (fuel + 1)
            (.top (a :: b :: hs) ents)).run w).1 =
            .ok (gStableSort (kfR srcs r κ rev) (rs.set i (v :: t')).flatten) := by
          rw [drain_step srcs r κ impl rev fuel _ _ _ w _ hs1]
          exact ih _ _ _ _ (inv_some srcs r κ rev hr hI i hi x v t' hrs hroot) (by omega)
        rw [Eff.run_bind_fst hdr]
        rfl
      | nil =>
        obtain ⟨v0, h', hpop⟩ := pyHeappop_ok
          (heapOrd rev (fun p q => entLtP r κ.isSome (phiE ents p) (phiE ents q))) _ hne
        have hd : (srcs.getD i []).drop (w.getD i 0) = [] := by rw [hI.pos i hi, hrs]; rfl
        have hs1 := top_step_none srcs r κ impl rev hr _ ents w i x hne hroot hd v0 h' hpop
        have hdr : ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (fuel + 1)
            (.top (a :: b :: hs) ents)).run w).1 =
            .ok (gStableSort (kfR srcs r κ rev) (rs.set i []).flatten) := by
          rw [drain_step srcs r κ impl rev fuel _ _ _ w _ hs1]
          exact ih _ _ _ _ (inv_none srcs r κ rev hr hI i hi x hrs hroot v0 h' hpop) (by omega)
        rw [Eff.run_bind_fst hdr]
        rfl

/-! ### The first `next()` and the theorem -/

include hr in
theorem start_step :
    (mergeStep (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) .start).run (srcs.map (fun _ => 0)) =
      (.ok (ytop (Accel.pyHeapify (heapOrd rev (fun i j => entLtP r κ.isSome (phiE (mEntsN srcs κ rev srcs) i)
          (phiE (mEntsN srcs κ rev srcs) j))) (List.range (mEntsN srcs κ rev srcs).length)) (mEntsN srcs κ rev srcs)),
        srcs.map (fun l => min 1 l.length)) := by
  have hinit := mergeInit_mEnv srcs r κ (if rev then -1 else 1) (List.range srcs.length) [] (srcs.map (fun _ => 0))
    (fun i _ => by simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases srcs[i]? <;> rfl)
    List.nodup_range
  rw [foldl_set_range] at hinit
  simp only [List.nil_append] at hinit
  have hE : (List.range srcs.length).filterMap (entFor srcs κ (if rev then -1 else 1)) = mEntsN srcs κ rev srcs := rfl
  rw [hE] at hinit
  have hcmp : entLtI (mEnv srcs r) (κ.map (pureKeyG (W := List Nat))).isSome (mEntsN srcs κ rev srcs) =
      fun i j => pure (entLtP r κ.isSome (phiE (mEntsN srcs κ rev srcs) i) (phiE (mEntsN srcs κ rev srcs) j)) := by
    rw [Option.isSome_map, entLtI_mEnv srcs r hr]
  apply mergeStep_ok_of_body
  simp only [mergeBody, mits]
  rw [zipIdx_map_src, Eff.run_bind_ok hinit, hcmp, Eff.run_bind_ok (hHeapify_pure impl rev _ _ _),
    reraise_ok, Eff.pure_bind]
  exact mergeYieldTop_run _ _ _

include hr in
theorem inv_start
    (hs : ∀ i < srcs.length, (srcs.getD i []).Pairwise (fun a b => kfR srcs r κ rev a ≤ kfR srcs r κ rev b)) :
    MInv srcs r κ rev (Accel.pyHeapify (heapOrd rev (fun i j => entLtP r κ.isSome (phiE (mEntsN srcs κ rev srcs) i)
          (phiE (mEntsN srcs κ rev srcs) j))) (List.range (mEntsN srcs κ rev srcs).length))
      (mEntsN srcs κ rev srcs) (srcs.map (fun l => min 1 l.length)) srcs := by
  have hsw := strictWeak_heapOrd (strictWeak_entLtP hr κ.isSome) rev
  have hm : (Accel.pyHeapify (heapOrd rev (fun i j => entLtP r κ.isSome (phiE (mEntsN srcs κ rev srcs) i)
          (phiE (mEntsN srcs κ rev srcs) j))) (List.range (mEntsN srcs κ rev srcs).length)).map
        (phiE (mEntsN srcs κ rev srcs)) =
      Accel.pyHeapify (heapOrd rev (entLtP r κ.isSome)) (mEntsN srcs κ rev srcs) := by
    conv => rhs; rw [← range_map_getD (mEntsN srcs κ rev srcs)]
    rw [pyHeapify_mapR (fun i => (mEntsN srcs κ rev srcs).getD i default) (heapOrd rev (entLtP r κ.isSome)),
      ← heapOrd_comp]
    rfl
  obtain ⟨hheap, hperm⟩ := Accel.pyHeapify_correct hsw (mEntsN srcs κ rev srcs)
  constructor
  · rfl
  · simp
  · intro i hi
    have : (srcs.map (fun l => min 1 l.length)).getD i 0 = min 1 (srcs.getD i []).length := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [this]
    generalize srcs.getD i [] = l
    cases l <;> simp
  · intro _ _ _ h; exact h
  · exact hs
  · intro id hid
    have := (pyHeapify_perm _ _).mem_iff.1 hid
    simpa using this
  · rw [hm]; exact hperm
  · rw [hm]; exact hheap

end main

/-- The input order in `MergeIsSorted` is the order on `kfR`. -/
theorem le_kfR {srcs : List (List α)} {r : α → α → Bool} {κ : Option (α → α)} (rev : Bool)
    (hr : Accel.StrictWeak r) {a b : α} (ha : kOf κ a ∈ KUm srcs κ) (hb : kOf κ b ∈ KUm srcs κ) :
    (if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a)) =
      decide (kfR srcs r κ rev a ≤ kfR srcs r κ rev b) := by
  cases rev
  · simp only [Bool.false_eq_true, if_false, kfR]
    rw [rank_spec hr (KUm srcs κ) hb ha]
    rw [Bool.eq_iff_iff]
    simp
  · simp only [if_true, kfR]
    rw [rank_spec hr (KUm srcs κ) ha hb]
    rw [Bool.eq_iff_iff]
    simp

theorem mergeIsSorted_proven : MergeIsSorted := by
  intro α _ _ srcs r κ impl rev fuel hr hf hsorted
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  have hs := start_step srcs r κ impl rev hr
  have hd := drain_step srcs r κ impl rev f' .start _ _ _ _ hs
  show ((mergeDrain (mEnv srcs r) impl (κ.map pureKeyG) rev (mits srcs) (f' + 1) .start).run
    (srcs.map (fun _ => 0))).1 = _
  rw [hd]
  have hmemK : ∀ a ∈ srcs.flatten, kOf κ a ∈ KUm srcs κ := fun a ha => List.mem_map.2 ⟨a, ha, rfl⟩
  have hsorted' : ∀ i < srcs.length,
      (srcs.getD i []).Pairwise (fun a b => kfR srcs r κ rev a ≤ kfR srcs r κ rev b) := by
    intro i hi
    have hl : srcs.getD i [] ∈ srcs := getD_mem_of srcs i hi
    refine (hsorted _ hl).imp_of_mem (fun {a b} ha hb hab => ?_)
    have hka := hmemK a (List.mem_flatten.2 ⟨_, hl, ha⟩)
    have hkb := hmemK b (List.mem_flatten.2 ⟨_, hl, hb⟩)
    rw [le_kfR rev hr hka hkb] at hab
    simpa using hab
  rw [yRun_sorted srcs r κ impl rev hr f' _ _ _ srcs (inv_start srcs r κ rev hr hsorted')
    (by rw [List.length_flatten]; omega)]
  congr 1
  have := List.map_mergeSort (f := id) (l := srcs.flatten)
    (r := fun a b => if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))
    (s := fun a b => decide (kfR srcs r κ rev a ≤ kfR srcs r κ rev b))
    (fun a ha b hb => le_kfR rev hr (hmemK a ha) (hmemK b hb))
  simp only [List.map_id] at this
  exact this.symm

/-! ### `next.__self__` free -/

/-- `MergeIsSorted` for every iterator, not only those whose `__next__` is a bound method:
the honest inputs of `mEnv` with `next.__self__` (`SEnv.selfOf`, Lib/heapq.py:383 / :408) any
callback. A valid iterator may define `__next__` as a staticmethod (the iterator protocol only
asks that `it.__next__()` work); then `it.__next__` is a plain function and `next.__self__`
raises `AttributeError: 'function' object has no attribute '__self__'`. Source: the docstring
(Lib/heapq.py:331-345), which promises the merge for any sorted iterables. -/
def MergeIsSortedAnyIter : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (srcs : List (List α)) (r : α → α → Bool)
    (κ : Option (α → α)) (impl rev : Bool) (fuel : Nat) (selfOf : MO → Eff (List Nat) PyExc MO),
    Accel.StrictWeak r →
    (srcs.map List.length).sum + 2 < fuel →
    (∀ l ∈ srcs, l.Pairwise (fun a b => if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))) →
    ((mergeDrain { mEnv srcs r with selfOf := selfOf } impl (κ.map pureKeyG) rev
        ((List.range srcs.length).map MO.src) fuel .start).run (srcs.map (fun _ => 0))).1 =
      .ok (srcs.flatten.mergeSort (fun a b => if rev then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a)))

/-- What CPython's `next.__self__` does for an iterator whose `__next__` is a staticmethod. -/
def selfOfStatic : MO → Eff (List Nat) PyExc MO :=
  fun _ => Eff.raise (.named "AttributeError" "'function' object has no attribute '__self__'")

/-- `list(merge(It()))` for an iterator `It()` over `[1, 2, 3]` whose `__next__` is a
staticmethod: the first `next()` yields `1`, the second reaches `yield from next.__self__` with
only this input left and raises `AttributeError`, for both heap implementations. -/
theorem mergeStatic_run (impl : Bool) :
    ((mergeDrain { mEnv [[(1 : Int), 2, 3]] intLtB with selfOf := selfOfStatic } impl none false
        ((List.range 1).map MO.src) 10 .start).run [0]).1 =
      .error (.named "AttributeError" "'function' object has no attribute '__self__'") := by
  cases impl <;> decide +kernel

theorem mergeIsSortedAnyIter_refuted : ¬ MergeIsSortedAnyIter := by
  intro h
  have := h Int [[1, 2, 3]] intLtB none false false 10 selfOfStatic strictWeak_intLtB (by decide) (by decide)
  have h2 := (mergeStatic_run false).symm.trans this
  cases h2

end PyLean.Accel.Heapq
