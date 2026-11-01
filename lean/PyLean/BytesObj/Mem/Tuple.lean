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
    (hb : ∀ i ∈ idx, ssizeMin ≤ i ∧ i ≤ ssizeMax) (hr : InRange idx (sh.drop dim)) :
    tupleLoop v dim (idx.map fun i => KeyElem.obj (.int i)) ptr st =
      (.ok (pathAddr st.mem idx (strs.drop dim) (subDrop dim v.suboffsets) ptr), st) := by
  induction idx generalizing dim ptr with
  | nil => rfl
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
          .ok (adjustPtr st.mem (ptr + strs.getD dim 0 * i) v.suboffsets dim) := by
        simp only [lookupDimension, hsh, hst, Option.getD_some, hn]
        rw [if_neg (by omega), if_neg (by omega)]
      have hdrop : sh.drop (dim + 1) = ns := by
        have : sh.drop (dim + 1) = (sh.drop dim).drop 1 := by simp [List.drop_drop, Nat.add_comm]
        rw [this, hd]
        rfl
      simp only [List.map_cons, tupleLoop, elemIndex, M.bind_app, numberIndex, M.pure_app, M.lift, hk,
        M.get, hlook]
      rw [ih (dim + 1) _ (fun j hj => hb j (by simp [hj])) (by rw [hdrop]; exact hr')]
      simp only [pathAddr, getD_drop_zero, adjustPtr_drop, subTail_subDrop]
      congr 2
      simp [List.drop_drop, Nat.add_comm]

/-- `m[i, j, ...]` with one in-range index per dimension is `m.tolist()[i][j]...`, for every
view of a native format, any number of dimensions, any strides and suboffsets
(`ptr_from_tuple`, `memory_item_multi`, `is_multiindex`, :2423-2448, :2483-2506). Hypotheses:
a live view whose arrays have `ndim` entries. -/
def TupleItem : Prop :=
  ∀ (st : St) (self : Nat) (c : Char) (sh strs idx : List Int),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    (st.mv self).view.shape = some sh → (st.mv self).view.strides = some strs → sh ≠ [] →
    sh.length = (st.mv self).view.ndim → InRange idx sh →
    (∀ i ∈ idx, ssizeMin ≤ i ∧ i ≤ ssizeMax) →
    ∃ (t : Tree) (x : Item), memoryviewTolist self st = (.ok t, st) ∧
      t.at (idx.map Int.toNat) = some x ∧
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

theorem tupleItem_proven : TupleItem := by
  intro st self c sh strs idx hl hf hc hsh hst hne hn hr hb
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  have hnd : ¬ (st.mv self).view.ndim = 0 := by
    rw [← hn]
    intro h
    exact hne (List.length_eq_zero_iff.1 h)
  have hlen := inRange_length _ _ hr
  have hmi : isMultiindex (idx.map fun i => KeyElem.obj (.int i)) = true := by
    simp [isMultiindex, Obj.isIndex]
  have hloop := tupleLoop_ints st (st.mv self).view sh strs hsh hst idx 0 (st.mv self).view.buf hb
    (by simpa using hr)
  simp only [List.drop_zero] at hloop
  have hsd : subDrop 0 (st.mv self).view.suboffsets = (st.mv self).view.suboffsets := by
    cases (st.mv self).view.suboffsets <;> rfl
  rw [hsd] at hloop
  refine ⟨_, g (pathAddr st.mem idx strs (st.mv self).view.suboffsets (st.mv self).view.buf),
    memoryviewTolist_eq st self c sh strs g hl hf hg hsh hst hne hn,
    treeOf_at _ _ _ _ _ _ _ hne hr, ?_⟩
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
    (hit : ∀ x ∈ items, x.length = it) (hds : (it : Int) ≤ ds ∨ ds ≤ -(it : Int))
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
        have := step_apart ds it j hds
        exact ⟨hj1.1, by omega⟩
    | succ k =>
      have e : p + ((k + 1 : Nat) : Int) * ds = p + ds + (k : Int) * ds := by
        rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega
      rw [e]
      simp only [List.getElem_cons_succ]
      apply ih (p + ds) _ (fun y hy => hit y (by simp [hy])) _ k
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
    (it ≤ ds ∨ ds ≤ -it) →
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
  rw [writeItems_read it.toNat ds _ dptr dm (by simp [rdBytes_length]) (by rw [hi]; exact hds) ?_ k hlenk]
  · exact walk_map_getElem ss n.toNat sptr it.toNat sm k (by omega) hlenk
  · intro j hj
    simp [walk_length] at hj
    have := hb j (by omega)
    rw [hi]
    exact this

end PyLean.BytesObj.Mem
