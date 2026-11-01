import PyLean.BytesObj.Mem.Items

/-!
What a view contains: the item addresses in C order, `tolist`, and the copy routines
behind `tobytes`, for every number of dimensions, stride and suboffset.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `n` pointers from `p` in steps of `step`: the `for` loops of the walkers. -/
def walk (step : Int) : Nat → Int → List Int
  | 0, _ => []
  | n + 1, p => p :: walk step n (p + step)

/-- The addresses of the items, in C order, through the suboffsets. -/
def addrs (m : Mem) : List Int → List Int → Option (List Int) → Int → List Int
  | [], _, _, _ => []
  | [n], st, subs, ptr => (walk (st.getD 0 0) n.toNat ptr).map (adjustPtr m · subs 0)
  | n :: sh@(_ :: _), st, subs, ptr =>
    (walk (st.getD 0 0) n.toNat ptr).flatMap fun p =>
      addrs m sh (st.drop 1) (subTail subs) (adjustPtr m p subs 0)

/-- The nested list `tolist` builds from an unpacking function that cannot fail. -/
def treeOf (m : Mem) (g : Int → Item) : List Int → List Int → Option (List Int) → Int → Tree
  | [], _, _, _ => .node []
  | [n], st, subs, ptr =>
    .node ((walk (st.getD 0 0) n.toNat ptr).map fun p => .leaf (g (adjustPtr m p subs 0)))
  | n :: sh@(_ :: _), st, subs, ptr =>
    .node ((walk (st.getD 0 0) n.toNat ptr).map fun p =>
      treeOf m g sh (st.drop 1) (subTail subs) (adjustPtr m p subs 0))

mutual
  /-- The items of a nested list, in order. -/
  def Tree.flat : Tree → List Item
    | .leaf i => [i]
    | .node l => Tree.flatL l
  def Tree.flatL : List Tree → List Item
    | [] => []
    | t :: ts => t.flat ++ Tree.flatL ts
end

theorem tolistBase_ok {α : Type} (m : Mem) (g : Int → α) (stride : Int) (subs : Option (List Int))
    (n : Nat) (ptr : Int) :
    tolistBase m (fun p => .ok (g p)) stride subs n ptr =
      .ok ((walk stride n ptr).map fun p => g (adjustPtr m p subs 0)) := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih =>
    simp only [tolistBase, bind, Except.bind, ih, pure, Except.pure, walk, List.map_cons]

theorem tolistRec_ok (m : Mem) (g : Int → Item) (sh st : List Int) (subs : Option (List Int))
    (ptr : Int) :
    tolistRec m (fun p => .ok (g p)) sh st subs ptr = .ok (treeOf m g sh st subs ptr) := by
  induction sh generalizing st subs ptr with
  | nil => simp only [tolistRec, treeOf]
  | cons n xs ih =>
    match xs, ih with
    | [], _ =>
      simp only [tolistRec, treeOf, tolistBase_ok, Functor.map, Except.map, List.map_map]
      rfl
    | x :: xs, ih =>
      simp only [tolistRec, treeOf, ih, tolistBase_ok, Functor.map, Except.map]

theorem flatL_map_leaf (l : List Int) (g : Int → Item) :
    Tree.flatL (l.map fun p => Tree.leaf (g p)) = l.map g := by
  induction l with
  | nil => simp [Tree.flatL]
  | cons x xs ih => simp [Tree.flatL, Tree.flat, ih]

theorem flatL_map_flatMap (l : List Int) (f : Int → Tree) :
    Tree.flatL (l.map f) = l.flatMap fun p => (f p).flat := by
  induction l with
  | nil => simp [Tree.flatL]
  | cons x xs ih => simp [Tree.flatL, ih]

/-- `tolist`, flattened, is the items at `addrs`. -/
theorem treeOf_flat (m : Mem) (g : Int → Item) (sh st : List Int) (subs : Option (List Int))
    (ptr : Int) : (treeOf m g sh st subs ptr).flat = (addrs m sh st subs ptr).map g := by
  induction sh generalizing st subs ptr with
  | nil => simp [treeOf, Tree.flat, Tree.flatL, addrs]
  | cons n xs ih =>
    match xs, ih with
    | [], _ =>
      simp only [treeOf, Tree.flat, addrs, List.map_map]
      exact flatL_map_leaf _ _
    | x :: xs, ih =>
      simp only [treeOf, Tree.flat, addrs, List.map_flatMap, ih, flatL_map_flatMap]

/-! ## Row sizes -/

def prod : List Int → Int
  | [] => 1
  | x :: l => x * prod l

theorem prod_append (l : List Int) (n : Int) : prod (l ++ [n]) = prod l * n := by
  induction l with
  | nil => simp [prod]
  | cons x xs ih => simp only [List.cons_append, prod, ih, Int.mul_assoc]

theorem prod_reverse (l : List Int) : prod l.reverse = prod l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, prod_append, ih, prod]
    exact Int.mul_comm _ _

theorem fStrides_snoc (sd : Int) (l : List Int) (n : Int) :
    fStrides sd (l ++ [n]) = fStrides sd l ++ [sd * prod l] := by
  induction l generalizing sd with
  | nil => simp [fStrides, prod]
  | cons x xs ih =>
    simp only [List.cons_append, fStrides, ih, prod, Int.mul_assoc]

theorem cStrides_cons (it n : Int) (sh : List Int) :
    cStrides it (n :: sh) = (it * prod sh) :: cStrides it sh := by
  unfold cStrides
  rw [List.reverse_cons, fStrides_snoc, List.reverse_append, prod_reverse]
  rfl

theorem cStrides_single (it n : Int) : cStrides it [n] = [it] := by
  simp [cStrides, fStrides]

theorem prod_nonneg (l : List Int) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ prod l := by
  induction l with
  | nil => simp [prod]
  | cons x xs ih =>
    simp only [prod]
    exact Int.mul_nonneg (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem walk_length (step : Int) (n : Nat) (p : Int) : (walk step n p).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [walk, ih]

theorem flatMap_const_len {α : Type} (l : List Int) (f : Int → List α) (r : Nat)
    (h : ∀ p, (f p).length = r) : (l.flatMap f).length = l.length * r := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, h, ih, List.length_cons]
    rw [Nat.add_mul]
    omega

/-- All the bytes of a sub-array, in C order. -/
def flatBytes (m : Mem) (it : Int) (sh st : List Int) (subs : Option (List Int)) (ptr : Int) :
    List Nat :=
  (addrs m sh st subs ptr).flatMap fun p => rdBytes m p it.toNat

theorem flatBytes_length (m : Mem) (it : Int) (hit : 0 ≤ it) (sh st : List Int)
    (subs : Option (List Int)) (ptr : Int) (hne : sh ≠ []) (h : ∀ x ∈ sh, 0 ≤ x) :
    ((flatBytes m it sh st subs ptr).length : Int) = prod sh * it := by
  induction sh generalizing st subs ptr with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match xs, ih with
    | [], _ =>
      have hn := h n (by simp)
      simp only [flatBytes, addrs]
      rw [flatMap_const_len _ _ it.toNat (fun p => rdBytes_length _ _ _)]
      simp only [List.length_map, walk_length, prod, Int.mul_one]
      rw [Int.natCast_mul, Int.toNat_of_nonneg hn, Int.toNat_of_nonneg hit]
    | x :: xs, ih =>
      have hn := h n (by simp)
      have hrow : ∀ p, ((addrs m (x :: xs) (st.drop 1) (subTail subs) (adjustPtr m p subs 0)).flatMap
          fun p => rdBytes m p it.toNat).length = (prod (x :: xs) * it).toNat := by
        intro p
        have := ih (st.drop 1) (subTail subs) (adjustPtr m p subs 0) (by simp)
          (fun y hy => h y (List.mem_cons_of_mem _ hy))
        unfold flatBytes at this
        omega
      simp only [flatBytes, addrs, List.flatMap_assoc]
      rw [flatMap_const_len _ _ _ hrow, walk_length, Int.natCast_mul, Int.toNat_of_nonneg hn]
      rw [Int.toNat_of_nonneg (Int.mul_nonneg (prod_nonneg _ fun y hy => h y (by simp [hy])) hit)]
      simp only [prod, Int.mul_assoc]

/-! ## The copy into a contiguous destination -/

theorem adjustPtr_none (m : Mem) (p : Int) (d : Nat) : adjustPtr m p none d = p := rfl

theorem readItems_eq (sm : Mem) (it : Nat) (stride : Int) (subs : Option (List Int)) (n : Nat)
    (p : Int) : readItems sm it stride subs n p =
      (walk stride n p).map fun q => rdBytes sm (adjustPtr sm q subs 0) it := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [readItems, walk, ih]

theorem writeItems_contig (it : Nat) (items : List (List Nat)) (dptr : Int) (dm : Mem)
    (h : ∀ x ∈ items, x.length = it) :
    writeItems it it none items dptr dm = wrBytes dm dptr items.flatten := by
  induction items generalizing dptr dm with
  | nil => rfl
  | cons x xs ih =>
    simp only [writeItems, adjustPtr_none, List.flatten_cons]
    rw [← wrBytes_append, h x (by simp)]
    exact ih _ _ fun y hy => h y (by simp [hy])

theorem rdBytes_walk (sm : Mem) (it : Nat) (k : Nat) (p : Int) :
    rdBytes sm p (k * it) = (walk it k p).flatMap fun q => rdBytes sm q it := by
  induction k generalizing p with
  | zero => simp [walk, rdBytes]
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm, rdBytes_append]
    simp only [walk, List.flatMap_cons]
    rw [ih]

/-- `last_dim_is_contiguous` for the source, on the arrays from the current dimension. -/
def LastOK (it : Int) (sh st : List Int) (subs : Option (List Int)) : Prop :=
  st.getD (sh.length - 1) 0 = it ∧ (subs.getD []).getD (sh.length - 1) (-1) < 0

theorem adjust_lastOK (m : Mem) (p : Int) (subs : Option (List Int))
    (h : (subs.getD []).getD 0 (-1) < 0) : adjustPtr m p subs 0 = p := by
  cases subs with
  | none => rfl
  | some s =>
    simp only [Option.getD_some] at h
    simp only [adjustPtr]
    rw [if_neg (by omega)]

theorem map_adjust_id (m : Mem) (l : List Int) (subs : Option (List Int))
    (h : (subs.getD []).getD 0 (-1) < 0) : l.map (adjustPtr m · subs 0) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, adjust_lastOK m x subs h, ih]

theorem copyBase_spec (n it dptr sptr s : Int) (ssub : Option (List Int)) (useMem : Bool)
    (sm dm : Mem) (hit : 0 ≤ it) (hn : 0 ≤ n)
    (hu : useMem = false → s = it ∧ (ssub.getD []).getD 0 (-1) < 0) :
    copyBase n it dptr it none sptr s ssub useMem sm dm =
      wrBytes dm dptr (flatBytes sm it [n] [s] ssub sptr) := by
  have hflat : flatBytes sm it [n] [s] ssub sptr =
      ((walk s n.toNat sptr).map (adjustPtr sm · ssub 0)).flatMap fun p => rdBytes sm p it.toNat := by
    simp only [flatBytes, addrs, List.getD_cons_zero]
  cases useMem with
  | false =>
    obtain ⟨rfl, hs⟩ := hu rfl
    simp only [copyBase, Bool.not_false, ↓reduceIte]
    rw [hflat, map_adjust_id _ _ _ hs]
    congr 1
    have e : (n * s).toNat = n.toNat * s.toNat := by
      rw [Int.toNat_mul hn hit]
    rw [e]
    have := rdBytes_walk sm s.toNat n.toNat sptr
    rw [Int.toNat_of_nonneg hit] at this
    exact this
  | true =>
    simp only [copyBase, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [readItems_eq, hflat]
    have hw := writeItems_contig it.toNat
      ((walk s n.toNat sptr).map fun q => rdBytes sm (adjustPtr sm q ssub 0) it.toNat) dptr dm
      (by simp [rdBytes_length])
    rw [Int.toNat_of_nonneg hit] at hw
    rw [hw]
    simp [List.flatMap_map, List.flatMap_def]
    rfl

theorem copyLoop_rows (dstep sstep : Int) (body : Int → Int → Mem → Mem) (R : Int → List Nat)
    (hb : ∀ d s dm, body d s dm = wrBytes dm d (R s))
    (hl : ∀ s, ((R s).length : Int) = dstep) (k : Nat) (dptr sptr : Int) (dm : Mem) :
    copyLoop dstep sstep body k dptr sptr dm = wrBytes dm dptr ((walk sstep k sptr).flatMap R) := by
  induction k generalizing dptr sptr dm with
  | zero => rfl
  | succ k ih =>
    simp only [copyLoop, walk, List.flatMap_cons]
    rw [ih, hb, ← wrBytes_append, hl]

theorem lastOK_tail (it n x : Int) (xs st : List Int) (subs : Option (List Int))
    (h : LastOK it (n :: x :: xs) st subs) : LastOK it (x :: xs) (st.drop 1) (subTail subs) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · simp only [List.length_cons, Nat.add_sub_cancel] at h1 ⊢
    rw [← h1]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
  · simp only [List.length_cons, Nat.add_sub_cancel] at h2 ⊢
    cases subs with
    | none => exact h2
    | some s =>
      simp only [subTail, Option.map_some, Option.getD_some] at h2 ⊢
      have : (s.drop 1).getD xs.length (-1) = s.getD (xs.length + 1) (-1) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
      rw [this]
      exact h2

/-- `copy_rec` into a C-contiguous destination writes the items in C order. -/
theorem copyRec_spec (it : Int) (hit : 0 ≤ it) (useMem : Bool) (sm : Mem) (sh : List Int)
    (hne : sh ≠ []) (hnn : ∀ x ∈ sh, 0 ≤ x) (dptr sptr : Int) (sst : List Int)
    (ssub : Option (List Int)) (dm : Mem) (hu : useMem = false → LastOK it sh sst ssub) :
    copyRec it useMem sm sh dptr (cStrides it sh) none sptr sst ssub dm =
      wrBytes dm dptr (flatBytes sm it sh sst ssub sptr) := by
  induction sh generalizing dptr sptr sst ssub dm with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match xs, ih with
    | [], _ =>
      have hflat : flatBytes sm it [n] sst ssub sptr = flatBytes sm it [n] [sst.getD 0 0] ssub sptr := by
        simp only [flatBytes, addrs, List.getD_cons_zero]
      simp only [copyRec, cStrides_single, List.getD_cons_zero]
      rw [hflat]
      exact copyBase_spec _ _ _ _ _ _ _ _ _ hit (hnn n (by simp)) (fun h => by
        have := hu h
        simpa [LastOK] using this)
    | x :: xs, ih =>
      have hdrop : (cStrides it (n :: x :: xs)).drop 1 = cStrides it (x :: xs) := by
        rw [cStrides_cons]; rfl
      have hhead : (cStrides it (n :: x :: xs)).getD 0 0 = it * prod (x :: xs) := by
        rw [cStrides_cons]; rfl
      simp only [copyRec, hdrop, hhead, adjustPtr_none]
      have hnnT : ∀ y ∈ x :: xs, 0 ≤ y := fun y hy => hnn y (List.mem_cons_of_mem _ hy)
      have hrow : ∀ d s dm', copyRec it useMem sm (x :: xs) d (cStrides it (x :: xs)) (subTail none)
          (adjustPtr sm s ssub 0) (sst.drop 1) (subTail ssub) dm' =
          wrBytes dm' d (flatBytes sm it (x :: xs) (sst.drop 1) (subTail ssub) (adjustPtr sm s ssub 0)) := by
        intro d s dm'
        exact ih (by simp) hnnT _ _ _ _ _ (fun h => lastOK_tail _ _ _ _ _ _ (hu h))
      rw [copyLoop_rows _ _ _ (fun s => flatBytes sm it (x :: xs) (sst.drop 1) (subTail ssub)
        (adjustPtr sm s ssub 0)) hrow (fun s => by
          rw [flatBytes_length _ _ hit _ _ _ _ (by simp) hnnT]
          exact Int.mul_comm _ _)]
      simp only [flatBytes, addrs, List.flatMap_assoc]

theorem shapeLoop_refl (l : List Int) : shapeLoop l l = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [shapeLoop, ne_eq, not_true_eq_false, ↓reduceIte, ih]
    split <;> rfl

theorem rdBytes_self (L : Mem) (p : Nat) (n : Nat) (h : p + n = L.length) :
    rdBytes L p n = L.drop p := by
  induction n generalizing p with
  | zero =>
    have : L.drop p = [] := by
      apply List.drop_eq_nil_of_le
      omega
    rw [this]
    rfl
  | succ n ih =>
    simp only [rdBytes]
    have hp : p < L.length := by omega
    have e : ((p : Int) + 1) = ((p + 1 : Nat) : Int) := by omega
    rw [e, ih (p + 1) (by omega), List.drop_eq_getElem_cons hp]
    simp [rdByte, List.getD_eq_getElem?_getD, hp]

theorem wrBytes_fresh (n : Nat) (bs : List Nat) (h : bs.length = n) :
    wrBytes (List.replicate n 0) 0 bs = bs := by
  have hlen : (wrBytes (List.replicate n 0) 0 bs).length = n := by
    rw [wrBytes_length]; simp
  have h1 := rdBytes_wrBytes (List.replicate n 0) 0 bs (by omega) (by simp; omega)
  have h2 : rdBytes (wrBytes (List.replicate n 0) 0 bs) 0 bs.length = wrBytes (List.replicate n 0) 0 bs := by
    simpa using rdBytes_self (wrBytes (List.replicate n 0) 0 bs) 0 bs.length (by omega)
  rw [← h2]
  exact h1

/-- `m.tobytes()` when `PyBuffer_ToContiguous` has to copy: for every view with full
information, of any number of dimensions, any strides and any suboffsets,
`buffer_to_contiguous` in order `'C'` gives the items in row-major order, each `itemsize`
bytes, which is the order of `tolist` (`TolistFlat`). Docs of `tobytes`: "`order` ... 'C'
... the data of the original array is converted to C order". Hypotheses: the type
invariants of a buffer (arrays of length `ndim`, `len == product(shape) * itemsize`,
`shape[i] >= 0`, `itemsize > 0`). -/
def TobytesC : Prop :=
  ∀ (sm : Mem) (v : Buf) (sh st : List Int), v.shape = some sh → v.strides = some st → sh ≠ [] →
    sh.length = v.ndim → (∀ x ∈ sh, 0 ≤ x) → 0 < v.itemsize → v.len = prod sh * v.itemsize →
    bufferToContiguous sm v 'C' = .ok (flatBytes sm v.itemsize sh st v.suboffsets v.buf)

theorem equiv_self (v v' : Buf) (sh : List Int) (hsh : v.shape = some sh) (hn : sh.length = v.ndim)
    (h1 : v'.shape = v.shape) (h2 : v'.ndim = v.ndim) (h3 : v'.format = v.format)
    (h4 : v'.itemsize = v.itemsize) : equivStructure v' v = .ok () := by
  have hf : equivFormat v' v = true := by simp [equivFormat, h3, h4]
  have hs : equivShape v' v = true := by
    simp only [equivShape, h1, h2, hsh, Option.getD_some, beq_self_eq_true, Bool.true_and]
    rw [← hn, List.take_length]
    exact shapeLoop_refl sh
  simp [equivStructure, hf, hs]

theorem lastOK_of (v dest : Buf) (sh st : List Int) (hst : v.strides = some st) (hn : sh.length = v.ndim)
    (h : (!lastDimIsContiguous dest v) = false) : LastOK v.itemsize sh st v.suboffsets := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, lastDimIsContiguous, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨-, h1⟩, -⟩, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hst] at h2
    simpa [hn] using h2
  · unfold haveSubInLast at h1
    rw [hn]
    cases hs : v.suboffsets with
    | none => simp
    | some s =>
      rw [hs] at h1
      have h1' : ¬ (s.getD (v.ndim - 1) (-1) ≥ 0) := by simpa using h1
      simp only [Option.getD_some]
      omega

theorem tobytesC_proven : TobytesC := by
  intro sm v sh st hsh hst hne hn hnn hit hlen
  obtain ⟨dest, hdest⟩ : ∃ d : Buf, d =
      { v with buf := 0, strides := some (cStrides v.itemsize sh), suboffsets := none } := ⟨_, rfl⟩
  have e1 : bufferToContiguous sm v 'C' = copyBuffer sm (List.replicate v.len.toNat 0) dest v := by
    rw [hdest]
    unfold bufferToContiguous
    simp only [hsh, Option.getD_some, true_or, ↓reduceIte]
  have hds : dest.shape = some sh := by rw [hdest]; exact hsh
  have hdst : dest.strides = some (cStrides v.itemsize sh) := by rw [hdest]
  have hdsub : dest.suboffsets = none := by rw [hdest]
  have hdb : dest.buf = 0 := by rw [hdest]
  have hdi : dest.itemsize = v.itemsize := by rw [hdest]
  have heq := equiv_self v dest sh hsh hn (by rw [hds, hsh]) (by rw [hdest]) (by rw [hdest]) hdi
  rw [e1]
  simp only [copyBuffer, bind, Except.bind, heq, pure, Except.pure, hds, hdst, hdsub, hdb, hdi,
    Option.getD_some, hst]
  have hl := flatBytes_length sm v.itemsize (by omega) sh st v.suboffsets v.buf hne hnn
  have hc := copyRec_spec v.itemsize (by omega) (!lastDimIsContiguous dest v) sm sh hne hnn 0 v.buf st
    v.suboffsets (List.replicate v.len.toNat 0) (lastOK_of v dest sh st hst hn)
  rw [hc]
  congr 1
  apply wrBytes_fresh
  omega

/-- Every native format unpacks to something. -/
theorem native_total (m : Mem) (c : Char) (h : nativeChar c = true) :
    ∃ g : Int → Item, ∀ p, unpackRaw m p [c] = .ok (g p) := by
  unfold nativeChar at h
  split at h
  all_goals first
    | (exact ⟨_, fun p => by simp only [unpackRaw, cc, List.getD_cons_zero]; rfl⟩)
    | (simp at h)

/-- `m.tolist()` for every view of a native format, of any dimension, shape, strides and
suboffsets: the items, flattened, are the native items at the addresses of `addrs`, and
nothing changes. Hypotheses: a live view whose arrays are present. -/
def TolistFlat : Prop :=
  ∀ (st : St) (self : Nat) (c : Char) (sh strs : List Int),
    baseInaccessible st self = false →
    adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    (st.mv self).view.shape = some sh → (st.mv self).view.strides = some strs →
    sh ≠ [] → sh.length = (st.mv self).view.ndim →
    ∃ (g : Int → Item) (t : Tree), (∀ p, unpackRaw st.mem p [c] = .ok (g p)) ∧
      memoryviewTolist self st = (.ok t, st) ∧
      t.flat = (addrs st.mem sh strs (st.mv self).view.suboffsets (st.mv self).view.buf).map g

theorem tolistFlat_proven : TolistFlat := by
  intro st self c sh strs hl hf hc hsh hst hne hn
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  have hfn : (fun p => (unpackSingle self p [c] st).1) = fun p => Except.ok (g p) := by
    funext p
    rw [unpackSingle_live _ _ _ _ hl, hg]
  have hnd : ¬ (st.mv self).view.ndim = 0 := by
    rw [← hn]
    intro h
    exact hne (List.length_eq_zero_iff.1 h)
  have hget : memoryviewTolist self st =
      if (st.mv self).view.ndim = 1 then
        match tolistBase st.mem (fun p => .ok (g p)) (((st.mv self).view.strides.getD []).getD 0 0)
            (st.mv self).view.suboffsets (((st.mv self).view.shape.getD []).getD 0 0).toNat
            (st.mv self).view.buf with
        | .ok l => (.ok (.node (l.map Tree.leaf)), st)
        | .error e => (.error e, st)
      else
        match tolistRec st.mem (fun p => .ok (g p)) ((st.mv self).view.shape.getD [])
            ((st.mv self).view.strides.getD []) (st.mv self).view.suboffsets (st.mv self).view.buf with
        | .ok t => (.ok t, st)
        | .error e => (.error e, st) := by
    simp only [memoryviewTolist, M.bind_app, checkReleased_ok _ _ hl, M.get, M.lift, hf, hnd,
      ↓reduceIte]
    simp only [hfn]
    split
    · rw [tolistBase_ok]
      rfl
    · rw [tolistRec_ok]
      rfl
  refine ⟨g, ?_⟩
  by_cases h1 : (st.mv self).view.ndim = 1
  · rw [h1] at hn
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 hn
    rw [hget, if_pos h1, hsh, hst]
    simp only [Option.getD_some, List.getD_cons_zero]
    rw [tolistBase_ok]
    refine ⟨_, hg, rfl, ?_⟩
    simp only [Tree.flat, addrs, List.map_map]
    have := flatL_map_leaf (walk (strs.getD 0 0) n.toNat (st.mv self).view.buf)
      (fun p => g (adjustPtr st.mem p (st.mv self).view.suboffsets 0))
    simpa [Function.comp_def] using this
  · rw [hget, if_neg h1, hsh, hst]
    simp only [Option.getD_some]
    rw [tolistRec_ok]
    exact ⟨_, hg, rfl, treeOf_flat _ _ _ _ _ _⟩

end PyLean.BytesObj.Mem
