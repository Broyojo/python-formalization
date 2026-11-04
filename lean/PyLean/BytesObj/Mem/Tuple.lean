import PyLean.BytesObj.Mem.Rest

/-!
`m[i, j, ...]` against `tolist`, and `copy_single`.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `tolist()[i][j]...`, as far as the path goes. -/
def Tree.at : Tree → List Nat → Option Item
  | .leaf x, [] => some x
  | .node l, i :: is =>
    match l[i]? with
    | some t => t.at is
    | none => none
  | _, _ => none

/-- The address a full index reaches, walking the dimensions as `ptr_from_tuple` does. -/
def pathAddr (m : Mem) : List Int → List Int → Option (List Int) → Int → Int
  | [], _, _, p => p
  | i :: is, st, subs, p =>
    pathAddr m is (st.drop 1) (subTail subs) (adjustPtr m (p + st.getD 0 0 * i) subs 0)

theorem walk_getElem (step : Int) (n : Nat) (p : Int) (i : Nat) (h : i < n) :
    (walk step n p)[i]? = some (p + step * i) := by
  induction n generalizing p i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [walk]
    | succ i =>
      simp only [walk, List.getElem?_cons_succ]
      rw [ih _ _ (by omega)]
      congr 1
      rw [Int.natCast_succ, Int.mul_add, Int.mul_one]
      omega

/-- In-range indices for the arrays from a dimension on. -/
def InRange : List Int → List Int → Prop
  | [], [] => True
  | i :: is, n :: ns => 0 ≤ i ∧ i < n ∧ InRange is ns
  | _, _ => False

/-- Indices that `lookup_dimension` accepts: `-n <= i < n`, in each dimension. -/
def InBounds : List Int → List Int → Prop
  | [], [] => True
  | i :: is, n :: ns => -n ≤ i ∧ i < n ∧ InBounds is ns
  | _, _ => False

/-- The positions those indices name. -/
def normIdx : List Int → List Int → List Int
  | i :: is, n :: ns => pos i n :: normIdx is ns
  | _, _ => []

theorem inRange_norm (idx sh : List Int) (h : InBounds idx sh) : InRange (normIdx idx sh) sh := by
  induction sh generalizing idx with
  | nil =>
    match idx, h with
    | [], _ => trivial
  | cons n ns ih =>
    match idx, h with
    | i :: is, ⟨h0, h1, hr⟩ =>
      refine ⟨?_, ?_, ih is hr⟩
      · unfold pos
        split <;> omega
      · unfold pos
        split <;> omega

theorem treeOf_at (m : Mem) (g : Int → Item) (sh idx strs : List Int) (subs : Option (List Int))
    (ptr : Int) (hne : sh ≠ []) (h : InRange idx sh) :
    (treeOf m g sh strs subs ptr).at (idx.map Int.toNat) = some (g (pathAddr m idx strs subs ptr)) := by
  induction sh generalizing idx strs subs ptr with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match idx, h with
    | i :: is, ⟨h0, h1, hr⟩ =>
      have hi : i.toNat < n.toNat := by omega
      have hw := walk_getElem (strs.getD 0 0) n.toNat ptr i.toNat hi
      rw [Int.toNat_of_nonneg h0] at hw
      match xs, ih, is, hr with
      | [], _, [], _ =>
        simp only [treeOf, List.map_cons, List.map_nil, Tree.at, List.getElem?_map, hw, Option.map_some,
          pathAddr]
      | x :: xs, ih, is, hr =>
        simp only [treeOf, List.map_cons, Tree.at, List.getElem?_map, hw, Option.map_some, pathAddr]
        exact ih is _ _ _ (by simp) hr

def subDrop (k : Nat) (s : Option (List Int)) : Option (List Int) := s.map (·.drop k)

theorem subTail_subDrop (k : Nat) (s : Option (List Int)) : subTail (subDrop k s) = subDrop (k + 1) s := by
  cases s with
  | none => rfl
  | some l => simp [subTail, subDrop, Nat.add_comm]

theorem adjustPtr_drop (m : Mem) (p : Int) (s : Option (List Int)) (k : Nat) :
    adjustPtr m p (subDrop k s) 0 = adjustPtr m p s k := by
  cases s with
  | none => rfl
  | some l =>
    simp [adjustPtr, subDrop, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_drop_zero (l : List Int) (k : Nat) : (l.drop k).getD 0 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem tupleLoop_ints (st : St) (v : Buf) (sh strs : List Int) (hsh : v.shape = some sh)
    (hst : v.strides = some strs) (idx : List Int) (dim : Nat) (ptr : Int)
    (hb : ∀ i ∈ idx, ssizeMin ≤ i ∧ i ≤ ssizeMax) (hr : InBounds idx (sh.drop dim)) :
    tupleLoop v dim (idx.map fun i => KeyElem.obj (.int i)) ptr st =
      (.ok (pathAddr st.mem (normIdx idx (sh.drop dim)) (strs.drop dim) (subDrop dim v.suboffsets) ptr), st) := by
  induction idx generalizing dim ptr with
  | nil =>
    cases hd : sh.drop dim <;> rfl
  | cons i is ih =>
    have hbi := hb i (by simp)
    have hk : keyAsSsize (.int i) i = .ok i := by simp [keyAsSsize, hbi]
    match hd : sh.drop dim, hr with
    | n :: ns, ⟨h0, h1, hr'⟩ =>
      have hn : sh.getD dim 0 = n := by
        have : (sh.drop dim).getD 0 0 = sh.getD dim 0 := getD_drop_zero _ _
        rw [← this, hd]
        rfl
      have hlook : lookupDimension st.mem v ptr dim i =
          .ok (adjustPtr st.mem (ptr + strs.getD dim 0 * pos i n) v.suboffsets dim) := by
        simp only [lookupDimension, hsh, hst, Option.getD_some, hn]
        unfold pos
        split <;> (rename_i hc) <;> rw [if_neg (by omega)]
      have hdrop : sh.drop (dim + 1) = ns := by
        have : sh.drop (dim + 1) = (sh.drop dim).drop 1 := by simp [List.drop_drop, Nat.add_comm]
        rw [this, hd]
        rfl
      simp only [List.map_cons, tupleLoop, elemIndex, M.bind_app, numberIndex, M.pure_app, M.lift, hk,
        M.get, hlook]
      rw [ih (dim + 1) _ (fun j hj => hb j (by simp [hj])) (by rw [hdrop]; exact hr'), hdrop]
      simp only [normIdx, pathAddr, getD_drop_zero, adjustPtr_drop, subTail_subDrop]
      congr 2
      simp [List.drop_drop, Nat.add_comm]

/-- `m[i, j, ...]` with one index per dimension, each `-n <= i < n`, is the item of
`m.tolist()` at those positions, a negative index counting from the end, for every view of a native
format, any number of dimensions, any strides and suboffsets (`ptr_from_tuple`,
`memory_item_multi`, `is_multiindex`, :2504-2528, :2564-2586). `TupleRefusals` is the rest. Hypotheses:
a live view whose arrays have `ndim` entries, and indices a `Py_ssize_t` can hold. -/
def TupleItem : Prop :=
  ∀ (st : St) (self : Nat) (c : Char) (sh strs idx : List Int),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    (st.mv self).view.shape = some sh → (st.mv self).view.strides = some strs → sh ≠ [] →
    sh.length = (st.mv self).view.ndim → InBounds idx sh →
    (∀ i ∈ idx, ssizeMin ≤ i ∧ i ≤ ssizeMax) →
    ∃ (t : Tree) (x : Item), memoryviewTolist self st = (.ok t, st) ∧
      t.at ((normIdx idx sh).map Int.toNat) = some x ∧
      memorySubscript self (.tuple (idx.map fun i => KeyElem.obj (.int i))) st = (.ok (.item x), st)

theorem inRange_length (a b : List Int) (h : InRange a b) : a.length = b.length := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [InRange])
  | cons x xs ih =>
    cases b with
    | nil => exact absurd h (by simp [InRange])
    | cons y ys =>
      simp only [List.length_cons]
      rw [ih _ h.2.2]

theorem inBounds_length (a b : List Int) (h : InBounds a b) : a.length = b.length := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [InBounds])
  | cons x xs ih =>
    cases b with
    | nil => exact absurd h (by simp [InBounds])
    | cons y ys =>
      simp only [List.length_cons]
      rw [ih _ h.2.2]

theorem tupleItem_proven : TupleItem := by
  intro st self c sh strs idx hl hf hc hsh hst hne hn hr hb
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  have hnd : ¬ (st.mv self).view.ndim = 0 := by
    rw [← hn]
    intro h
    exact hne (List.length_eq_zero_iff.1 h)
  have hlen := inBounds_length _ _ hr
  have hmi : isMultiindex (idx.map fun i => KeyElem.obj (.int i)) = true := by
    simp [isMultiindex, Obj.isIndex]
  have hloop := tupleLoop_ints st (st.mv self).view sh strs hsh hst idx 0 (st.mv self).view.buf hb
    (by simpa using hr)
  simp only [List.drop_zero] at hloop
  have hsd : subDrop 0 (st.mv self).view.suboffsets = (st.mv self).view.suboffsets := by
    cases (st.mv self).view.suboffsets <;> rfl
  rw [hsd] at hloop
  refine ⟨_, g (pathAddr st.mem (normIdx idx sh) strs (st.mv self).view.suboffsets (st.mv self).view.buf),
    memoryviewTolist_eq st self c sh strs g hl hf hg hsh hst hne hn,
    treeOf_at _ _ _ _ _ _ _ hne (inRange_norm _ _ hr), ?_⟩
  simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hl, M.get, hnd, ↓reduceIte, hmi,
    memoryItemMulti, M.lift, hf, M.pure_app]
  have hnl : ¬ (idx.map fun i => KeyElem.obj (.int i)).length < (st.mv self).view.ndim := by
    simp only [List.length_map]
    omega
  have hgt : ¬ (idx.map fun i => KeyElem.obj (.int i)).length > (st.mv self).view.ndim := by
    simp only [List.length_map]
    omega
  simp only [hnl, ↓reduceIte, ptrFromTuple, hgt, M.bind_app, M.pure_app, hloop,
    unpackSingle_live _ _ _ _ hl, hg]

/-- The walk stops at the first index out of bounds, and the indices after it are not looked at. -/
theorem tupleLoop_out (st : St) (v : Buf) (sh strs : List Int) (hsh : v.shape = some sh)
    (hst : v.strides = some strs) (pre post : List Int) (i : Int) (dim : Nat) (ptr : Int)
    (hb : ∀ j ∈ pre ++ i :: post, ssizeMin ≤ j ∧ j ≤ ssizeMax)
    (hp : InBounds pre ((sh.drop dim).take pre.length))
    (hi : ¬ (-(sh.getD (dim + pre.length) 0) ≤ i ∧ i < sh.getD (dim + pre.length) 0)) :
    tupleLoop v dim ((pre ++ i :: post).map fun i => KeyElem.obj (.int i)) ptr st =
      (.error (.indexError s!"index out of bounds on dimension {dim + pre.length + 1}"), st) := by
  induction pre generalizing dim ptr with
  | nil =>
    have hbi := hb i (by simp)
    have hk : keyAsSsize (.int i) i = .ok i := by simp [keyAsSsize, hbi]
    have hlook : lookupDimension st.mem v ptr dim i =
        .error (.indexError s!"index out of bounds on dimension {dim + 1}") := by
      simp only [lookupDimension, hsh, Option.getD_some]
      simp only [List.length_nil, Nat.add_zero] at hi
      rw [if_pos]
      split <;> omega
    simp only [List.nil_append, List.map_cons, tupleLoop, elemIndex, M.bind_app, numberIndex, M.pure_app,
      M.lift, hk, M.get, hlook]
    rfl
  | cons a as ih =>
    have hba := hb a (by simp)
    have hk : keyAsSsize (.int a) a = .ok a := by simp [keyAsSsize, hba]
    simp only [List.length_cons] at hp hi ⊢
    match hd : sh.drop dim, hp with
    | n :: ns, hp =>
      obtain ⟨h0, h1, hr'⟩ : -n ≤ a ∧ a < n ∧ InBounds as (ns.take as.length) := by
        simpa [InBounds] using hp
      have hn : sh.getD dim 0 = n := by
        have : (sh.drop dim).getD 0 0 = sh.getD dim 0 := getD_drop_zero _ _
        rw [← this, hd]
        rfl
      have hlook : lookupDimension st.mem v ptr dim a =
          .ok (adjustPtr st.mem (ptr + strs.getD dim 0 * pos a n) v.suboffsets dim) := by
        simp only [lookupDimension, hsh, hst, Option.getD_some, hn]
        unfold pos
        split <;> (rename_i hc) <;> rw [if_neg (by omega)]
      have hdrop : sh.drop (dim + 1) = ns := by
        have : sh.drop (dim + 1) = (sh.drop dim).drop 1 := by simp [List.drop_drop, Nat.add_comm]
        rw [this, hd]
        rfl
      simp only [List.cons_append, List.map_cons, tupleLoop, elemIndex, M.bind_app, numberIndex, M.pure_app,
        M.lift, hk, M.get, hlook]
      rw [ih (dim + 1) _ (fun j hj => hb j (by simp only [List.cons_append, List.mem_cons]; exact Or.inr hj))
        (by rw [hdrop]; exact hr') (by rw [show dim + 1 + as.length = dim + (as.length + 1) by omega]; exact hi)]
      simp only [show dim + 1 + as.length + 1 = dim + (as.length + 1) + 1 by omega]

/-- The refusals of `ptr_from_tuple`, :2509-2525, for a tuple of ints: more indices than dimensions is
a `TypeError` before any index is looked at; otherwise the first index out of bounds is an
`IndexError` naming its dimension, whatever follows it. Hypotheses: a live view whose arrays have
`ndim` entries, and ints a `Py_ssize_t` can hold; for the second case, one index per dimension
and all earlier ones in bounds, which is the case. -/
def TupleRefusals : Prop :=
  ∀ (st : St) (self : Nat) (fmt : List Char) (sh strs : List Int),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok fmt →
    (st.mv self).view.shape = some sh → (st.mv self).view.strides = some strs → sh ≠ [] →
    sh.length = (st.mv self).view.ndim →
    (∀ idx : List Int, (st.mv self).view.ndim < idx.length →
      memorySubscript self (.tuple (idx.map fun i => KeyElem.obj (.int i))) st =
        (.error (.typeError s!"cannot index {(st.mv self).view.ndim}-dimension view with {idx.length}-element tuple"), st)) ∧
    (∀ (pre post : List Int) (i : Int), (pre ++ i :: post).length = sh.length →
      (∀ j ∈ pre ++ i :: post, ssizeMin ≤ j ∧ j ≤ ssizeMax) → InBounds pre (sh.take pre.length) →
      ¬ (-(sh.getD pre.length 0) ≤ i ∧ i < sh.getD pre.length 0) →
      memorySubscript self (.tuple ((pre ++ i :: post).map fun i => KeyElem.obj (.int i))) st =
        (.error (.indexError s!"index out of bounds on dimension {pre.length + 1}"), st))

theorem tupleRefusals_proven : TupleRefusals := by
  intro st self fmt sh strs hl hf hsh hst hne hn
  have hnd : ¬ (st.mv self).view.ndim = 0 := by
    rw [← hn]
    intro h
    exact hne (List.length_eq_zero_iff.1 h)
  have hmi : ∀ l : List Int, isMultiindex (l.map fun i => KeyElem.obj (.int i)) = true := by
    intro l
    simp [isMultiindex, Obj.isIndex]
  constructor
  · intro idx hlen
    have hnl : ¬ idx.length < (st.mv self).view.ndim := by omega
    have hgt : idx.length > (st.mv self).view.ndim := hlen
    simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hl, M.get, hnd, ↓reduceIte, hmi,
      memoryItemMulti, M.lift, hf, M.pure_app, List.length_map, hnl, ptrFromTuple, hgt, M.throw_app]
  · intro pre post i hlen hb hp hi
    have hnl : ¬ ((pre ++ i :: post).map fun i => KeyElem.obj (.int i)).length < (st.mv self).view.ndim := by
      simp only [List.length_map]
      omega
    have hgt : ¬ ((pre ++ i :: post).map fun i => KeyElem.obj (.int i)).length > (st.mv self).view.ndim := by
      simp only [List.length_map]
      omega
    have hloop := tupleLoop_out st (st.mv self).view sh strs hsh hst pre post i 0 (st.mv self).view.buf hb
      (by simpa using hp) (by simpa using hi)
    simp only [Nat.zero_add] at hloop
    simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hl, M.get, hnd, ↓reduceIte, hmi,
      memoryItemMulti, M.lift, hf, M.pure_app, hnl, ptrFromTuple, hgt, hloop]

/-! ## `copy_single` -/

theorem writeItems_frame (it : Nat) (ds q : Int) (items : List (List Nat)) (p : Int) (dm : Mem)
    (hit : ∀ x ∈ items, x.length = it) (hq : 0 ≤ q)
    (h : ∀ j : Nat, j < items.length → 0 ≤ p + j * ds ∧
      (q + it ≤ p + j * ds ∨ p + j * ds + it ≤ q)) :
    rdBytes (writeItems it ds none items p dm) q it = rdBytes dm q it := by
  induction items generalizing p dm with
  | nil => rfl
  | cons x xs ih =>
    simp only [writeItems, adjustPtr_none]
    have h0 : 0 ≤ p ∧ (q + it ≤ p ∨ p + it ≤ q) := by simpa using h 0 (by simp)
    rw [ih (p + ds) _ (fun y hy => hit y (by simp [hy])) ?_]
    · apply rdBytes_out _ _ _ _ _ h0.1 hq
      rw [hit x (by simp)]
      omega
    · intro j hj
      have := h (j + 1) (by simp; omega)
      have e : p + ds + (j : Int) * ds = p + ((j + 1 : Nat) : Int) * ds := by
        rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega
      rw [e]
      exact this

theorem step_apart (ds : Int) (it : Nat) (j : Nat) (h : (it : Int) ≤ ds ∨ ds ≤ -(it : Int)) :
    (it : Int) ≤ ((j + 1 : Nat) : Int) * ds ∨ ((j + 1 : Nat) : Int) * ds ≤ -(it : Int) := by
  have e : ((j + 1 : Nat) : Int) * ds = (j : Int) * ds + ds := by
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
  rw [e]
  rcases h with h | h
  · left
    have : 0 ≤ (j : Int) * ds := Int.mul_nonneg (by omega) (by omega)
    omega
  · right
    have : 0 ≤ (j : Int) * (-ds) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg] at this
    omega

theorem writeItems_read (it : Nat) (ds : Int) (items : List (List Nat)) (p : Int) (dm : Mem)
    (hit : ∀ x ∈ items, x.length = it) (hds : items.length ≤ 1 ∨ (it : Int) ≤ ds ∨ ds ≤ -(it : Int))
    (hb : ∀ j : Nat, j < items.length → 0 ≤ p + j * ds ∧ p + j * ds + it ≤ dm.length)
    (k : Nat) (hk : k < items.length) :
    rdBytes (writeItems it ds none items p dm) (p + k * ds) it = items[k] := by
  induction items generalizing p dm k with
  | nil => simp at hk
  | cons x xs ih =>
    simp only [writeItems, adjustPtr_none]
    have hx := hit x (by simp)
    have hb0 : 0 ≤ p ∧ p + it ≤ dm.length := by simpa using hb 0 (by simp)
    have hlen : (wrBytes dm p x).length = dm.length := wrBytes_length _ _ _
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [show p + ((0 : Nat) : Int) * ds = p by simp]
      rw [writeItems_frame it ds p xs (p + ds) _ (fun y hy => hit y (by simp [hy])) hb0.1]
      · rw [← hx]
        exact rdBytes_wrBytes dm p x hb0.1 (by omega)
      · intro j hj
        have hj1 := hb (j + 1) (by simp; omega)
        have e : p + ds + (j : Int) * ds = p + ((j + 1 : Nat) : Int) * ds := by
          rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
          omega
        rw [e]
        have hapart : (it : Int) ≤ ds ∨ ds ≤ -(it : Int) := by
          rcases hds with h | h
          · simp only [List.length_cons] at h
            omega
          · exact h
        have := step_apart ds it j hapart
        exact ⟨hj1.1, by omega⟩
    | succ k =>
      have e : p + ((k + 1 : Nat) : Int) * ds = p + ds + (k : Int) * ds := by
        rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega
      rw [e]
      simp only [List.getElem_cons_succ]
      apply ih (p + ds) _ (fun y hy => hit y (by simp [hy]))
        (hds.elim (fun h => Or.inl (by simp only [List.length_cons] at h; omega)) Or.inr) _ k
      intro j hj
      have hj1 := hb (j + 1) (by simp; omega)
      have e2 : p + ds + (j : Int) * ds = p + ((j + 1 : Nat) : Int) * ds := by
        rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega
      rw [e2, hlen]
      exact hj1

/-- `dest[k] = src[k]` after `m[s] = src`, in the path that goes through the scratch buffer:
every byte of the source is read before the first write, so it holds for overlapping views
too; `sm` is the store before the copy. -/
def CopyStrided : Prop :=
  ∀ (sm dm : Mem) (n it dptr sptr ds ss : Int), 0 ≤ n → 0 < it →
    (n ≤ 1 ∨ it ≤ ds ∨ ds ≤ -it) →
    (∀ j : Nat, (j : Int) < n → 0 ≤ dptr + j * ds ∧ dptr + j * ds + it ≤ dm.length) →
    ∀ k : Nat, (k : Int) < n →
      rdBytes (copyBase n it dptr ds none sptr ss none true sm dm) (dptr + k * ds) it.toNat =
        rdBytes sm (sptr + k * ss) it.toNat

theorem walk_map_getElem (ss : Int) (n : Nat) (sptr : Int) (it : Nat) (sm : Mem) (k : Nat) (hk : k < n)
    (h : k < ((walk ss n sptr).map fun q => rdBytes sm (adjustPtr sm q none 0) it).length) :
    ((walk ss n sptr).map fun q => rdBytes sm (adjustPtr sm q none 0) it)[k] =
      rdBytes sm (sptr + k * ss) it := by
  have := walk_getElem ss n sptr k hk
  simp only [List.getElem_map]
  have hk' : k < (walk ss n sptr).length := by simpa using h
  have e : (walk ss n sptr)[k] = sptr + ss * k := by
    have h2 := List.getElem?_eq_getElem hk'
    rw [this] at h2
    exact (Option.some.inj h2).symm
  rw [e, adjustPtr_none, Int.mul_comm]

theorem copyStrided_proven : CopyStrided := by
  intro sm dm n it dptr sptr ds ss hn hit hds hb k hk
  simp only [copyBase, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readItems_eq]
  have hi : ((it.toNat : Nat) : Int) = it := Int.toNat_of_nonneg (by omega)
  have hlenk : k < ((walk ss n.toNat sptr).map fun q => rdBytes sm (adjustPtr sm q none 0) it.toNat).length := by
    simp [walk_length]
    omega
  rw [writeItems_read it.toNat ds _ dptr dm (by simp [rdBytes_length])
    (by
      rw [hi]
      rcases hds with h | h
      · exact Or.inl (by simp [walk_length]; omega)
      · exact Or.inr h) ?_ k hlenk]
  · exact walk_map_getElem ss n.toNat sptr it.toNat sm k (by omega) hlenk
  · intro j hj
    simp [walk_length] at hj
    have := hb j (by omega)
    rw [hi]
    exact this

end PyLean.BytesObj.Mem
