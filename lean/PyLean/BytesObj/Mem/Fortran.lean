import PyLean.BytesObj.Mem.NDim

/-!
`copy_rec` into a destination of any strides, as one write per item in index order; what that
means for Fortran order; and the `memcpy` branch of `PyBuffer_ToContiguous` on any number of
dimensions.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## Index tuples -/

/-- `k` numbers from `i` on. -/
def upto : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i => i :: upto k (i + 1)

theorem mem_upto (k i j : Nat) : j ∈ upto k i ↔ i ≤ j ∧ j < i + k := by
  induction k generalizing i with
  | zero =>
    simp only [upto, List.not_mem_nil, false_iff]
    omega
  | succ k ih =>
    simp only [upto, List.mem_cons, ih]
    omega

/-- The index tuples of a shape, the first index slowest: the order of `copy_rec`. -/
def idxs : List Int → List (List Nat)
  | [] => [[]]
  | n :: ns => (upto n.toNat 0).flatMap fun i => (idxs ns).map (i :: ·)

theorem mem_idxs_cons (n : Int) (ns : List Int) (idx : List Nat) :
    idx ∈ idxs (n :: ns) ↔ ∃ i is, idx = i :: is ∧ i < n.toNat ∧ is ∈ idxs ns := by
  simp only [idxs, List.mem_flatMap, List.mem_map, mem_upto]
  constructor
  · rintro ⟨i, ⟨-, hi⟩, is, his, rfl⟩
    exact ⟨i, is, rfl, by omega, his⟩
  · rintro ⟨i, is, rfl, hi, his⟩
    exact ⟨i, ⟨by omega, by omega⟩, is, his, rfl⟩

def toI (l : List Nat) : List Int := l.map fun (i : Nat) => (i : Int)

theorem walk_upto (step : Int) (k i : Nat) (p : Int) :
    walk step k (p + step * i) = (upto k i).map fun (j : Nat) => p + step * (j : Int) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [walk, upto, List.map_cons]
    have e : p + step * (i : Int) + step = p + step * ((i + 1 : Nat) : Int) := by
      rw [Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_assoc]
    rw [e, ih]

theorem walk_upto0 (step : Int) (k : Nat) (p : Int) :
    walk step k p = (upto k 0).map fun (j : Nat) => p + step * (j : Int) := by
  have := walk_upto step k 0 p
  simpa using this

/-! ## A sequence of writes -/

def writeSeq : List (Int × List Nat) → Mem → Mem
  | [], dm => dm
  | (d, x) :: r, dm => writeSeq r (wrBytes dm d x)

theorem writeSeq_append (a b : List (Int × List Nat)) (dm : Mem) :
    writeSeq (a ++ b) dm = writeSeq b (writeSeq a dm) := by
  induction a generalizing dm with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨d, y⟩ := x
    simp only [List.cons_append, writeSeq, ih]

theorem writeSeq_length (l : List (Int × List Nat)) (dm : Mem) : (writeSeq l dm).length = dm.length := by
  induction l generalizing dm with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨d, y⟩ := x
    simp only [writeSeq, ih, wrBytes_length]

theorem writeItems_seq (it : Nat) (ds : Int) (X : Nat → List Nat) (k i : Nat) (p : Int) (dm : Mem) :
    writeItems it ds none ((upto k i).map X) (p + ds * i) dm =
      writeSeq ((upto k i).map fun (j : Nat) => (p + ds * (j : Int), X j)) dm := by
  induction k generalizing i dm with
  | zero => rfl
  | succ k ih =>
    simp only [upto, List.map_cons, writeItems, writeSeq, adjustPtr_none]
    have e : p + ds * (i : Int) + ds = p + ds * ((i + 1 : Nat) : Int) := by
      rw [Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_assoc]
    rw [e, ih]

/-- `copy_base` into a destination with no suboffsets: one write per item. -/
theorem copyBase_seq (n it dptr ds sptr s : Int) (ssub : Option (List Int)) (useMem : Bool) (sm dm : Mem)
    (hit : 0 ≤ it) (hn : 0 ≤ n)
    (hu : useMem = false → ds = it ∧ s = it ∧ (ssub.getD []).getD 0 (-1) < 0) :
    copyBase n it dptr ds none sptr s ssub useMem sm dm =
      writeSeq ((upto n.toNat 0).map fun (j : Nat) =>
        (dptr + ds * (j : Int), rdBytes sm (adjustPtr sm (sptr + s * (j : Int)) ssub 0) it.toNat)) dm := by
  have htrue : copyBase n it dptr ds none sptr s ssub true sm dm =
      writeSeq ((upto n.toNat 0).map fun (j : Nat) =>
        (dptr + ds * (j : Int), rdBytes sm (adjustPtr sm (sptr + s * (j : Int)) ssub 0) it.toNat)) dm := by
    simp only [copyBase, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readItems_eq, walk_upto0, List.map_map]
    have := writeItems_seq it.toNat ds (fun (j : Nat) => rdBytes sm (adjustPtr sm (sptr + s * (j : Int)) ssub 0) it.toNat)
      n.toNat 0 dptr dm
    simpa [Function.comp_def] using this
  cases useMem with
  | true => exact htrue
  | false =>
    obtain ⟨rfl, rfl, h3⟩ := hu rfl
    rw [← htrue, copyBase_spec _ _ _ _ _ _ false _ _ hit hn (fun _ => ⟨rfl, h3⟩),
      copyBase_spec _ _ _ _ _ _ true _ _ hit hn (fun h => by cases h)]

theorem copyLoop_seq (dstep sstep : Int) (body : Int → Int → Mem → Mem) (W : Int → Int → List (Int × List Nat))
    (hb : ∀ d s dm, body d s dm = writeSeq (W d s) dm) (k i : Nat) (dptr sptr : Int) (dm : Mem) :
    copyLoop dstep sstep body k (dptr + dstep * i) (sptr + sstep * i) dm =
      writeSeq ((upto k i).flatMap fun (j : Nat) => W (dptr + dstep * (j : Int)) (sptr + sstep * (j : Int))) dm := by
  induction k generalizing i dm with
  | zero => rfl
  | succ k ih =>
    simp only [copyLoop, upto, List.flatMap_cons, writeSeq_append]
    have e : ∀ q step : Int, q + step * (i : Int) + step = q + step * ((i + 1 : Nat) : Int) := by
      intro q step
      rw [Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_assoc]
    rw [e, e, ih, hb]

theorem pathAddr_cons (m : Mem) (i : Nat) (is : List Nat) (st : List Int) (subs : Option (List Int)) (p : Int) :
    pathAddr m (toI (i :: is)) st subs p =
      pathAddr m (toI is) (st.drop 1) (subTail subs) (adjustPtr m (p + st.getD 0 0 * i) subs 0) := by
  simp only [toI, List.map_cons, pathAddr]

/-- `copy_rec`, @3.14.7:374-401, into a destination with any strides and no suboffsets: one write per
item, in index order, of the item the source has there. Any destination, so `C`, `F` and strided. -/
theorem copyRec_seq (it : Int) (hit : 0 ≤ it) (useMem : Bool) (sm : Mem) (sh : List Int) (hne : sh ≠ [])
    (hnn : ∀ x ∈ sh, 0 ≤ x) (dptr : Int) (dst : List Int) (sptr : Int) (sst : List Int)
    (ssub : Option (List Int)) (dm : Mem)
    (hu : useMem = false → dst.getD (sh.length - 1) 0 = it ∧ LastOK it sh sst ssub) :
    copyRec it useMem sm sh dptr dst none sptr sst ssub dm =
      writeSeq ((idxs sh).map fun idx =>
        (pathAddr [] (toI idx) dst none dptr,
         rdBytes sm (pathAddr sm (toI idx) sst ssub sptr) it.toNat)) dm := by
  induction sh generalizing dptr dst sptr sst ssub dm with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match xs, ih with
    | [], _ =>
      simp only [copyRec]
      rw [copyBase_seq _ _ _ _ _ _ _ _ _ _ hit (hnn n (by simp)) (fun h => by
        have := hu h
        simpa [LastOK] using this)]
      congr 1
      have hi : idxs [n] = (upto n.toNat 0).map fun (i : Nat) => [i] := by
        have hf : ∀ l : List Nat, (l.flatMap fun i => [[i]]) = l.map fun i => [i] := by
          intro l
          induction l with
          | nil => rfl
          | cons a as ih' =>
            simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append, ih']
        simp only [idxs, List.map_cons, List.map_nil]
        exact hf _
      rw [hi, List.map_map]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, toI, List.map_cons, List.map_nil, pathAddr, adjustPtr_none]
    | x :: xs, ih =>
      have htail : useMem = false → (dst.drop 1).getD ((x :: xs).length - 1) 0 = it ∧
          LastOK it (x :: xs) (sst.drop 1) (subTail ssub) := by
        intro h
        obtain ⟨h1, h2⟩ := hu h
        refine ⟨?_, lastOK_tail _ _ _ _ _ _ h2⟩
        rw [← h1]
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
      have hnnT : ∀ y ∈ x :: xs, 0 ≤ y := fun y hy => hnn y (List.mem_cons_of_mem _ hy)
      simp only [copyRec, adjustPtr_none]
      have hbody := fun d s dm' => ih (by simp) hnnT d (dst.drop 1) (adjustPtr sm s ssub 0) (sst.drop 1)
        (subTail ssub) dm' htail
      have hl := copyLoop_seq (dst.getD 0 0) (sst.getD 0 0)
        (fun d s dm' => copyRec it useMem sm (x :: xs) d (dst.drop 1) (subTail none)
          (adjustPtr sm s ssub 0) (sst.drop 1) (subTail ssub) dm')
        (fun d s => (idxs (x :: xs)).map fun idx =>
          (pathAddr [] (toI idx) (dst.drop 1) none d,
           rdBytes sm (pathAddr sm (toI idx) (sst.drop 1) (subTail ssub) (adjustPtr sm s ssub 0)) it.toNat))
        hbody n.toNat 0 dptr sptr dm
      have e0 : ((0 : Nat) : Int) = 0 := rfl
      simp only [e0, Int.mul_zero, Int.add_zero] at hl
      rw [hl]
      congr 1
      have hidx : idxs (n :: x :: xs) =
          (upto n.toNat 0).flatMap fun i => (idxs (x :: xs)).map (i :: ·) := by
        rw [idxs]
      rw [hidx, List.map_flatMap]
      congr 1
      funext j
      rw [List.map_map]
      apply List.map_congr_left
      intro idx _
      simp only [Function.comp, pathAddr_cons, adjustPtr_none]
      rfl

/-! ## Reading what the writes left -/

theorem writeSeq_frame (L : List (Int × List Nat)) (dm : Mem) (q : Int) (it : Nat) (hq : 0 ≤ q)
    (h : ∀ e ∈ L, 0 ≤ e.1 ∧ e.2.length = it ∧ (q + it ≤ e.1 ∨ e.1 + it ≤ q)) :
    rdBytes (writeSeq L dm) q it = rdBytes dm q it := by
  induction L generalizing dm with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨d, y⟩ := x
    obtain ⟨h1, h2, h3⟩ := h (d, y) (by simp)
    simp only [writeSeq]
    rw [ih _ (fun e he => h e (by simp [he]))]
    apply rdBytes_out _ _ _ _ _ h1 hq
    dsimp only at h2 h3
    rw [h2]
    exact h3

theorem writeSeq_read (L : List (Int × List Nat)) (dm : Mem) (it : Nat)
    (hw : ∀ e ∈ L, e.2.length = it) (hb : ∀ e ∈ L, 0 ≤ e.1 ∧ e.1 + it ≤ dm.length)
    (hp : L.Pairwise fun (a b : Int × List Nat) => a.1 + (it : Int) ≤ b.1 ∨ b.1 + (it : Int) ≤ a.1) :
    ∀ e ∈ L, rdBytes (writeSeq L dm) e.1 it = e.2 := by
  induction L generalizing dm with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨d, y⟩ := x
    rw [List.pairwise_cons] at hp
    intro e he
    simp only [writeSeq]
    have hb0 := hb (d, y) (by simp)
    have hy := hw (d, y) (by simp)
    dsimp only at hb0 hy
    rcases List.mem_cons.1 he with rfl | he'
    · dsimp only
      rw [writeSeq_frame _ _ _ _ hb0.1 (fun e' he'' => ⟨(hb e' (by simp [he''])).1, hw e' (by simp [he'']),
        hp.1 e' he''⟩)]
      rw [← hy]
      exact rdBytes_wrBytes dm d y hb0.1 (by omega)
    · exact ih _ (fun e' he'' => hw e' (by simp [he'']))
        (fun e' he'' => by
          have := hb e' (by simp [he''])
          rw [wrBytes_length]
          exact this) hp.2 e he'

/-! ## Fortran order -/

/-- The position of an index tuple in column-major order: the first index runs fastest. -/
def enc : List Int → List Nat → Nat
  | n :: ns, i :: is => i + n.toNat * enc ns is
  | _, _ => 0

theorem path_fortran (m : Mem) (sd : Int) (sh : List Int) (idx : List Nat) (h : idx ∈ idxs sh)
    (hnn : ∀ x ∈ sh, 0 ≤ x) (p : Int) :
    pathAddr m (toI idx) (fStrides sd sh) none p = p + sd * enc sh idx := by
  induction sh generalizing sd idx p with
  | nil =>
    simp only [idxs, List.mem_singleton] at h
    subst h
    simp [toI, pathAddr, enc]
  | cons n ns ih =>
    obtain ⟨i, is, rfl, hi, his⟩ := (mem_idxs_cons _ _ _).1 h
    have h0 := hnn n (by simp)
    rw [pathAddr_cons]
    simp only [fStrides, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, adjustPtr_none]
    rw [show subTail none = none from rfl, ih _ _ his (fun y hy => hnn y (by simp [hy])), enc]
    have e : ((i + n.toNat * enc ns is : Nat) : Int) = i + n * enc ns is := by
      rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg h0]
    rw [e, Int.mul_add, Int.mul_assoc, Int.add_assoc]

theorem enc_lt (sh : List Int) (idx : List Nat) (h : idx ∈ idxs sh) (hnn : ∀ x ∈ sh, 0 ≤ x) :
    (enc sh idx : Int) + 1 ≤ prod sh := by
  induction sh generalizing idx with
  | nil =>
    simp only [idxs, List.mem_singleton] at h
    subst h
    simp [enc, prod]
  | cons n ns ih =>
    obtain ⟨i, is, rfl, hi, his⟩ := (mem_idxs_cons _ _ _).1 h
    have h0 := hnn n (by simp)
    have h1 := ih is his (fun y hy => hnn y (by simp [hy]))
    have h2 : (n : Int) * ((enc ns is : Int) + 1) ≤ n * prod ns := Int.mul_le_mul_of_nonneg_left h1 h0
    rw [Int.mul_add, Int.mul_one] at h2
    simp only [enc, prod]
    rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg h0]
    omega

theorem enc_inj (sh : List Int) (a b : List Nat) (ha : a ∈ idxs sh) (hb : b ∈ idxs sh)
    (h : enc sh a = enc sh b) : a = b := by
  induction sh generalizing a b with
  | nil =>
    simp only [idxs, List.mem_singleton] at ha hb
    rw [ha, hb]
  | cons n ns ih =>
    obtain ⟨i, is, rfl, hi, his⟩ := (mem_idxs_cons _ _ _).1 ha
    obtain ⟨j, js, rfl, hj, hjs⟩ := (mem_idxs_cons _ _ _).1 hb
    simp only [enc] at h
    have h1 := congrArg (· % n.toNat) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1
    subst h1
    have h2 : n.toNat * enc ns is = n.toNat * enc ns js := by omega
    have h3 : enc ns is = enc ns js := Nat.eq_of_mul_eq_mul_left (by omega) h2
    rw [ih is js his hjs h3]

theorem idxs_pairwise (sh : List Int) : (idxs sh).Pairwise (· ≠ ·) := by
  induction sh with
  | nil => simp [idxs]
  | cons n ns ih =>
    have key : ∀ k i, ((upto k i).flatMap fun j => (idxs ns).map (j :: ·)).Pairwise (· ≠ ·) := by
      intro k
      induction k with
      | zero => intro i; simp [upto]
      | succ k ih2 =>
        intro i
        simp only [upto, List.flatMap_cons]
        rw [List.pairwise_append]
        refine ⟨?_, ih2 _, ?_⟩
        · rw [List.pairwise_map]
          exact ih.imp (fun h e => h (List.cons.inj e).2)
        · intro a ha b hb e
          obtain ⟨is, -, ris⟩ := List.mem_map.1 ha
          obtain ⟨j, hj, hm⟩ := List.mem_flatMap.1 hb
          obtain ⟨js, -, rjs⟩ := List.mem_map.1 hm
          rw [← ris, ← rjs] at e
          have h1 := (mem_upto _ _ _).1 hj
          have h2 := (List.cons.inj e).1
          omega
    exact key _ _

/-- The writes `copy_rec` makes into a Fortran-order destination at `base` leave each item at its
place: distinct index tuples go to distinct places, all inside the destination. -/
theorem fortran_writes (it : Int) (hit : 0 < it) (sh : List Int) (hnn : ∀ x ∈ sh, 0 ≤ x) (base : Int)
    (hbase : 0 ≤ base) (X : List Nat → List Nat) (hX : ∀ idx ∈ idxs sh, (X idx).length = it.toNat)
    (dm : Mem) (hdm : base + prod sh * it ≤ dm.length) (idx : List Nat) (hidx : idx ∈ idxs sh) :
    rdBytes (writeSeq ((idxs sh).map fun idx => (pathAddr [] (toI idx) (fStrides it sh) none base, X idx)) dm)
      (base + it * enc sh idx) it.toNat = X idx := by
  have hit' : ((it.toNat : Nat) : Int) = it := Int.toNat_of_nonneg (by omega)
  have := writeSeq_read ((idxs sh).map fun idx => (pathAddr [] (toI idx) (fStrides it sh) none base, X idx))
    dm it.toNat
    (by
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact hX a ha)
    (by
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      dsimp only
      rw [path_fortran [] it sh a ha hnn base, hit']
      have h1 := enc_lt sh a ha hnn
      have h2 : it * ((enc sh a : Int) + 1) ≤ it * prod sh := Int.mul_le_mul_of_nonneg_left h1 (by omega)
      rw [Int.mul_add, Int.mul_one, Int.mul_comm it (prod sh)] at h2
      have h3 : 0 ≤ it * (enc sh a : Int) := Int.mul_nonneg (by omega) (by omega)
      omega)
    (by
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem (fun {a b} ha hb hne => ?_) (idxs_pairwise sh)
      dsimp only
      rw [path_fortran [] it sh a ha hnn base, path_fortran [] it sh b hb hnn base, hit']
      have hne' : enc sh a ≠ enc sh b := fun e => hne (enc_inj sh a b ha hb e)
      by_cases hlt : enc sh a < enc sh b
      · left
        have h2 : it * ((enc sh a : Int) + 1) ≤ it * (enc sh b : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        rw [Int.mul_add, Int.mul_one] at h2
        omega
      · right
        have h2 : it * ((enc sh b : Int) + 1) ≤ it * (enc sh a : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        rw [Int.mul_add, Int.mul_one] at h2
        omega)
  have hx := this (_, _) (List.mem_map.2 ⟨idx, hidx, rfl⟩)
  dsimp only at hx
  rw [path_fortran [] it sh idx hidx hnn base] at hx
  exact hx

/-- `m.tobytes('F')`-style copy, `buffer_to_contiguous` in order `'F'` (@3.14.7:495-534, `copy_rec` with
`init_fortran_strides_from_shape`), for every view with full information, of any number of
dimensions, any strides and any suboffsets: the `len` bytes hold each item at its place in
column-major order, the first index running fastest. Docs of `tobytes`: "'F' ... the data of the
original array is converted to Fortran order". Hypotheses: the type invariants of a buffer. -/
def FortranCopy : Prop :=
  ∀ (sm : Mem) (v : Buf) (sh st : List Int), v.shape = some sh → v.strides = some st → sh ≠ [] →
    sh.length = v.ndim → (∀ x ∈ sh, 0 ≤ x) → 0 < v.itemsize → v.len = prod sh * v.itemsize →
    ∃ M, bufferToContiguous sm v 'F' = .ok M ∧ M.length = v.len.toNat ∧
      ∀ idx ∈ idxs sh, rdBytes M (v.itemsize * enc sh idx) v.itemsize.toNat =
        rdBytes sm (pathAddr sm (toI idx) st v.suboffsets v.buf) v.itemsize.toNat

theorem fortranCopy_proven : FortranCopy := by
  intro sm v sh st hsh hst hne hn hnn hit hlen
  obtain ⟨dest, hdest⟩ : ∃ d : Buf, d =
      { v with buf := 0, strides := some (fStrides v.itemsize sh), suboffsets := none } := ⟨_, rfl⟩
  have e1 : bufferToContiguous sm v 'F' = copyBuffer sm (List.replicate v.len.toNat 0) dest v := by
    rw [hdest]
    unfold bufferToContiguous
    simp [hsh]
  have hds : dest.shape = some sh := by rw [hdest]; exact hsh
  have hdst : dest.strides = some (fStrides v.itemsize sh) := by rw [hdest]
  have hdsub : dest.suboffsets = none := by rw [hdest]
  have hdb : dest.buf = 0 := by rw [hdest]
  have hdi : dest.itemsize = v.itemsize := by rw [hdest]
  have hdn : dest.ndim = v.ndim := by rw [hdest]
  have heq := equiv_self v dest sh hsh hn (by rw [hds, hsh]) hdn (by rw [hdest]) hdi
  have hu : (!lastDimIsContiguous dest v) = false →
      (fStrides v.itemsize sh).getD (sh.length - 1) 0 = v.itemsize ∧ LastOK v.itemsize sh st v.suboffsets := by
    intro h
    refine ⟨?_, lastOK_of v dest sh st hst hn h⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, lastDimIsContiguous, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨-, h1⟩, -⟩ := h
    rw [hdst, hdn, hdi, ← hn] at h1
    simpa using h1
  have hc := copyRec_seq v.itemsize (by omega) (!lastDimIsContiguous dest v) sm sh hne hnn 0
    (fStrides v.itemsize sh) v.buf st v.suboffsets (List.replicate v.len.toNat 0) hu
  have hb : bufferToContiguous sm v 'F' = .ok (writeSeq ((idxs sh).map fun idx =>
      (pathAddr [] (toI idx) (fStrides v.itemsize sh) none 0,
       rdBytes sm (pathAddr sm (toI idx) st v.suboffsets v.buf) v.itemsize.toNat))
      (List.replicate v.len.toNat 0)) := by
    rw [e1]
    simp only [copyBuffer, bind, Except.bind, heq, pure, Except.pure, hds, hdst, hdsub, hdb, hdi,
      Option.getD_some, hst]
    rw [hc]
  refine ⟨_, hb, ?_, fun idx hidx => ?_⟩
  · rw [writeSeq_length]
    simp
  · have hlenN : (0 : Int) ≤ v.len := by
      rw [hlen]
      exact Int.mul_nonneg (prod_nonneg _ hnn) (by omega)
    have := fortran_writes v.itemsize hit sh hnn 0 (by omega)
      (fun idx => rdBytes sm (pathAddr sm (toI idx) st v.suboffsets v.buf) v.itemsize.toNat)
      (fun idx _ => rdBytes_length _ _ _) (List.replicate v.len.toNat 0) (by simp; omega) idx hidx
    simpa using this

/-! ## The `memcpy` branch on any number of dimensions -/

theorem getD_drop_one (st : List Int) (k : Nat) : (st.drop 1).getD k 0 = st.getD (k + 1) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem prod_take_succ (xs : List Int) (k : Nat) (hk : k < xs.length) :
    prod (xs.take (k + 1)) = prod (xs.take k) * xs.getD k 0 := by
  have e : xs.take (k + 1) = xs.take k ++ [xs.getD k 0] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk]
    simp [List.getD_eq_getElem?_getD, hk]
  rw [e, prod_append]

/-- `_IsCContiguous`, walked from the last dimension, read from the first. -/
theorem cLoop_cons (n : Int) (xs st : List Int) (k : Nat) (sd : Int) (hk : k ≤ xs.length) :
    cLoop (n :: xs) st (k + 1) sd = true ↔
      cLoop xs (st.drop 1) k sd = true ∧ ¬ (n > 1 ∧ st.getD 0 0 ≠ sd * prod (xs.take k)) := by
  induction k generalizing sd with
  | zero =>
    simp only [cLoop, List.getD_cons_zero, List.take_zero, prod, Int.mul_one, true_and]
    split <;> simp_all
  | succ k ih =>
    have h1 : (n :: xs).getD (k + 1) 0 = xs.getD k 0 := by
      simp [List.getD_eq_getElem?_getD]
    have hlt : k < xs.length := by omega
    have hR : cLoop xs (st.drop 1) (k + 1) sd =
        if xs.getD k 0 > 1 ∧ st.getD (k + 1) 0 ≠ sd then false
        else cLoop xs (st.drop 1) k (sd * xs.getD k 0) := by
      rw [cLoop, getD_drop_one]
    have hL : cLoop (n :: xs) st (k + 1 + 1) sd =
        if xs.getD k 0 > 1 ∧ st.getD (k + 1) 0 ≠ sd then false
        else cLoop (n :: xs) st (k + 1) (sd * xs.getD k 0) := by
      rw [cLoop, h1]
    rw [hL, hR]
    by_cases hc : xs.getD k 0 > 1 ∧ st.getD (k + 1) 0 ≠ sd
    · rw [if_pos hc, if_pos hc]
      simp
    · rw [if_neg hc, if_neg hc, ih _ (by omega), prod_take_succ xs k hlt]
      rw [Int.mul_assoc, Int.mul_comm (xs.getD k 0) (prod (xs.take k))]

theorem walk_append (it : Int) (a b : Nat) (p : Int) :
    walk it (a + b) p = walk it a p ++ walk it b (p + it * a) := by
  induction a generalizing p with
  | zero => simp [walk]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [walk, List.cons_append]
    rw [ih]
    congr 3
    rw [Int.natCast_succ, Int.mul_add, Int.mul_one]
    omega

theorem walk_flat (it : Int) (P N : Nat) (p : Int) :
    (walk (it * P) N p).flatMap (fun q => walk it P q) = walk it (N * P) p := by
  induction N generalizing p with
  | zero => simp [walk]
  | succ N ih =>
    simp only [walk, List.flatMap_cons]
    rw [ih, Nat.succ_mul, Nat.add_comm, walk_append]

theorem walk_one (s : Int) (p : Int) : walk s 1 p = [p] := rfl

/-- A C-contiguous array with no empty dimension has its items one after another. -/
theorem addrs_contig (m : Mem) (it : Int) (sh st : List Int) (hne : sh ≠ []) (hpos : ∀ x ∈ sh, 1 ≤ x)
    (h : cLoop sh st sh.length it = true) (p : Int) :
    addrs m sh st none p = walk it (prod sh).toNat p := by
  induction sh generalizing st p with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    have hn := hpos n (by simp)
    have hsplit := (cLoop_cons n xs st xs.length it (by omega)).1 h
    rw [List.take_length] at hsplit
    obtain ⟨h1, h2⟩ := hsplit
    match xs, ih, hpos, h1, h2 with
    | [], _, _, _, h2 =>
      simp only [addrs, prod, Int.mul_one]
      simp only [prod, Int.mul_one] at h2
      by_cases h3 : n > 1
      · have h4 : st.getD 0 0 = it := by
          by_cases h5 : st.getD 0 0 = it
          · exact h5
          · exact absurd ⟨h3, h5⟩ h2
        rw [h4]
        simp [adjustPtr_none]
      · have h4 : n.toNat = 1 := by omega
        rw [h4]
        simp [walk, adjustPtr_none]
    | x :: xs, ih, hpos, h1, h2 =>
      have hT : ∀ y ∈ x :: xs, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
      have hrow := fun q => ih (st.drop 1) (by simp) hT h1 q
      have hP : 0 ≤ prod (x :: xs) := prod_nonneg _ (fun y hy => by have := hT y hy; omega)
      obtain ⟨P, hPe⟩ : ∃ P : Nat, prod (x :: xs) = (P : Int) := ⟨(prod (x :: xs)).toNat, by omega⟩
      simp only [addrs, adjustPtr_none]
      rw [show subTail none = none from rfl]
      simp only [hrow, hPe, Int.toNat_natCast]
      have hprod : (prod (n :: x :: xs)).toNat = n.toNat * P := by
        have e : prod (n :: x :: xs) = n * prod (x :: xs) := rfl
        rw [e, hPe, Int.toNat_mul (by omega) (by omega), Int.toNat_natCast]
      rw [hprod]
      by_cases h3 : n > 1
      · have h4 : st.getD 0 0 = it * (P : Int) := by
          by_cases h5 : st.getD 0 0 = it * prod (x :: xs)
          · rw [h5, hPe]
          · exact absurd ⟨h3, h5⟩ h2
        rw [h4]
        exact walk_flat it P n.toNat p
      · have h4 : n.toNat = 1 := by omega
        rw [h4]
        simp [walk]

theorem prod_zero (sh : List Int) (h : (0 : Int) ∈ sh) : prod sh = 0 := by
  induction sh with
  | nil => simp at h
  | cons a as ih =>
    simp only [prod]
    rcases List.mem_cons.1 h with rfl | h1
    · simp
    · rw [ih h1, Int.mul_zero]

/-- The two branches of `PyBuffer_ToContiguous`, @3.14.7:1062-1065 and @3.14.7:1084, for a C-contiguous view of
any number of dimensions: `memcpy` gives the row-major walk. -/
theorem tobytesContigND_proven : TobytesContigND := by
  intro m v sh st hsh hst hne hn hnn hit hlen hsub hc
  have hF := flatBytes_length m v.itemsize (by omega) sh st none v.buf hne hnn
  by_cases hz : v.len = 0
  · have hnil : flatBytes m v.itemsize sh st none v.buf = [] := by
      apply List.length_eq_zero_iff.1
      rw [hz] at hlen
      rw [← hlen] at hF
      omega
    rw [hnil, hz]
    rfl
  · have hpos : ∀ x ∈ sh, 1 ≤ x := by
      intro x hx
      have h0 := hnn x hx
      by_cases h1 : x = 0
      · subst h1
        rw [prod_zero sh hx, Int.zero_mul] at hlen
        exact absurd hlen hz
      · omega
    have hloop : cLoop sh st sh.length v.itemsize = true := by
      simpa [pyBufferIsContiguous, hsub, isCContiguous, hz, hst, hsh, hn] using hc
    have ha := addrs_contig m v.itemsize sh st hne hpos hloop v.buf
    have hit' : ((v.itemsize.toNat : Nat) : Int) = v.itemsize := Int.toNat_of_nonneg (by omega)
    have hP : 0 ≤ prod sh := prod_nonneg _ hnn
    have hl : v.len.toNat = (prod sh).toNat * v.itemsize.toNat := by
      rw [hlen, Int.toNat_mul hP (by omega)]
    unfold flatBytes
    rw [ha, hl]
    have := rdBytes_walk m v.itemsize.toNat (prod sh).toNat v.buf
    rw [hit'] at this
    exact this

/-! ## `tobytes` in each order -/

theorem path_fortran_loop (m : Mem) (sd : Int) (sh st : List Int) (idx : List Nat) (h : idx ∈ idxs sh)
    (hnn : ∀ x ∈ sh, 0 ≤ x) (hf : fLoop sh st sd = true) (p : Int) :
    pathAddr m (toI idx) st none p = p + sd * enc sh idx := by
  induction sh generalizing sd st idx p with
  | nil =>
    simp only [idxs, List.mem_singleton] at h
    subst h
    simp [toI, pathAddr, enc]
  | cons n ns ih =>
    obtain ⟨i, is, rfl, hi, his⟩ := (mem_idxs_cons _ _ _).1 h
    have h0 := hnn n (by simp)
    have key : ¬ (n > 1 ∧ st.getD 0 0 ≠ sd) ∧ fLoop ns (st.drop 1) (sd * n) = true := by
      cases st with
      | nil =>
        simp only [fLoop] at hf
        split at hf
        · simp at hf
        · rename_i hc
          exact ⟨by simpa using hc, hf⟩
      | cons s ss =>
        simp only [fLoop] at hf
        split at hf
        · simp at hf
        · rename_i hc
          exact ⟨by simpa using hc, by simpa using hf⟩
    obtain ⟨hk1, hk2⟩ := key
    rw [pathAddr_cons, adjustPtr_none, show subTail none = none from rfl,
      ih _ _ _ his (fun y hy => hnn y (by simp [hy])) hk2]
    have hstep : st.getD 0 0 * (i : Int) = sd * (i : Int) := by
      by_cases h3 : n > 1
      · have h4 : st.getD 0 0 = sd := by
          by_cases h5 : st.getD 0 0 = sd
          · exact h5
          · exact absurd ⟨h3, h5⟩ hk1
        rw [h4]
      · have h4 : i = 0 := by omega
        subst h4
        simp
    rw [hstep, enc]
    have e : ((i + n.toNat * enc ns is : Nat) : Int) = i + n * enc ns is := by
      rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg h0]
    rw [e, Int.mul_add, Int.mul_assoc, Int.add_assoc]

theorem rdByte_rdBytes (m : Mem) (p q : Int) (L : Nat) (h0 : 0 ≤ q) (h1 : q < L) :
    rdByte (rdBytes m p L) q = rdByte m (p + q) := by
  induction L generalizing p q with
  | zero => omega
  | succ L ih =>
    by_cases hq : q = 0
    · subst hq
      simp [rdBytes, rdByte]
    · have hq' : q.toNat = (q - 1).toNat + 1 := by omega
      have := ih (p + 1) (q - 1) (by omega) (by omega)
      unfold rdByte at this ⊢
      simp only [rdBytes, hq', List.getD_cons_succ]
      rw [this]
      congr 2
      omega

theorem rdBytes_rdBytes (m : Mem) (p q : Int) (L n : Nat) (h0 : 0 ≤ q) (h1 : q + n ≤ L) :
    rdBytes (rdBytes m p L) q n = rdBytes m (p + q) n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [rdBytes]
    rw [rdByte_rdBytes m p q L h0 (by omega), ih (q + 1) (by omega) (by omega), Int.add_assoc]

theorem bufferToContiguous_A (sm : Mem) (v : Buf) : bufferToContiguous sm v 'A' = bufferToContiguous sm v 'C' := by
  simp [bufferToContiguous]

/-- `m.tobytes(order)` for every live view of any number of dimensions, strides and suboffsets, and
the `order` of `memoryview_tobytes_impl`, @3.14.7:2286-2300. `'C'` and no order give the items in row-major
order. `'F'` gives each item at its place in column-major order. `'A'` gives the memory as it is if
that is contiguous in either order, and row-major order otherwise. The length check of
`PyBuffer_ToContiguous`, @3.14.7:1056-1060, refuses any other length. Hypotheses: the type invariants of a
buffer (`Full`, positive itemsize, `len == product(shape) * itemsize`). -/
def TobytesOrders : Prop :=
  ∀ (st : St) (self : Nat) (sh strs : List Int), baseInaccessible st self = false →
    let v := (st.mv self).view
    Full v → v.shape = some sh → v.strides = some strs → sh ≠ [] → (∀ x ∈ sh, 0 ≤ x) → 0 < v.itemsize →
    v.len = prod sh * v.itemsize →
    memoryviewTobytes self none st = (.ok (flatBytes st.mem v.itemsize sh strs v.suboffsets v.buf), st) ∧
    (∃ M, memoryviewTobytes self (some ['F']) st = (.ok M, st) ∧ M.length = v.len.toNat ∧
      ∀ idx ∈ idxs sh, rdBytes M (v.itemsize * enc sh idx) v.itemsize.toNat =
        rdBytes st.mem (pathAddr st.mem (toI idx) strs v.suboffsets v.buf) v.itemsize.toNat) ∧
    (pyBufferIsContiguous v 'A' = true →
      memoryviewTobytes self (some ['A']) st = (.ok (rdBytes st.mem v.buf v.len.toNat), st)) ∧
    (pyBufferIsContiguous v 'A' = false → memoryviewTobytes self (some ['A']) st =
      (.ok (flatBytes st.mem v.itemsize sh strs v.suboffsets v.buf), st)) ∧
    (∀ l o, l ≠ v.len → pyBufferToContiguous st.mem v l o =
      .error (.valueError "PyBuffer_ToContiguous: len != view->len"))

theorem tobytesOrders_proven : TobytesOrders := by
  intro st self sh strs hl
  dsimp only
  intro hfull hsh hst hne hnn hit hlen
  have hrank : sh.length = (st.mv self).view.ndim := by
    rcases hfull.arrays with ⟨-, h4, -⟩ | ⟨a, b, -, h4, -, h5, -⟩
    · rw [hsh] at h4
      cases h4
    · rw [hsh] at h5
      simp only [Option.some.injEq] at h5
      subst h5
      exact h4
  have hgo : ∀ o, pyBufferIsContiguous (st.mv self).view o = false →
      pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len o =
        bufferToContiguous st.mem (st.mv self).view o := by
    intro o hc
    have hfb := (fb_eq_copy (st.mv self).view).trans (viewCopy_full _ hfull)
    rcases hi : initShapeStrides (st.mv self).view with ⟨a, b⟩
    rw [hi] at hfb
    simp only [pyBufferToContiguous, ne_eq, not_true_eq_false, ↓reduceIte, hc, Bool.false_eq_true, hi]
    dsimp only at hfb ⊢
    rw [hfb]
  have hmem : ∀ o, pyBufferIsContiguous (st.mv self).view o = true →
      pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len o =
        .ok (rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat) := by
    intro o hc
    simp [pyBufferToContiguous, hc]
  have hto : ∀ o b, parseOrder o = .ok b →
      memoryviewTobytes self o st = (pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len b, st) := by
    intro o b h
    simp only [memoryviewTobytes, M.bind_app, checkReleased_ok _ _ hl, M.lift, h, M.get]
  have hC := tobytesC_proven st.mem (st.mv self).view sh strs hsh hst hne hrank hnn hit hlen
  have hcflat : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' =
      .ok (flatBytes st.mem (st.mv self).view.itemsize sh strs (st.mv self).view.suboffsets
        (st.mv self).view.buf) := by
    by_cases hc : pyBufferIsContiguous (st.mv self).view 'C' = true
    · have hsb : (st.mv self).view.suboffsets = none := by
        cases hs : (st.mv self).view.suboffsets with
        | none => rfl
        | some l => simp [pyBufferIsContiguous, hs] at hc
      rw [hmem _ hc, hsb, tobytesContigND_proven st.mem (st.mv self).view sh strs hsh hst hne hrank hnn hit
        hlen hsb hc]
    · rw [hgo _ (by simpa using hc), hC]
  refine ⟨?_, ?_, fun hc => ?_, fun hc => ?_, fun l o hne' => ?_⟩
  · rw [hto none 'C' rfl, hcflat]
  · obtain ⟨M, h1, h2, h3⟩ := fortranCopy_proven st.mem (st.mv self).view sh strs hsh hst hne hrank hnn hit hlen
    by_cases hc : pyBufferIsContiguous (st.mv self).view 'F' = true
    · refine ⟨rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat, ?_, rdBytes_length _ _ _, ?_⟩
      · rw [hto (some ['F']) 'F' rfl, hmem _ hc]
      · intro idx hidx
        have hsb : (st.mv self).view.suboffsets = none := by
          cases hs : (st.mv self).view.suboffsets with
          | none => rfl
          | some l => simp [pyBufferIsContiguous, hs] at hc
        have hlt := enc_lt sh idx hidx hnn
        have hP : 0 < prod sh := by omega
        have hit' : (((st.mv self).view.itemsize.toNat : Nat) : Int) = (st.mv self).view.itemsize :=
          Int.toNat_of_nonneg (by omega)
        have hL0 : (0 : Int) < (st.mv self).view.len := by
          rw [hlen]
          exact Int.mul_pos hP hit
        have hfl : fLoop sh strs (st.mv self).view.itemsize = true := by
          have hne0 : (st.mv self).view.len ≠ 0 := by omega
          simpa [pyBufferIsContiguous, hsb, isFortranContiguous, hne0, hst, hsh] using hc
        rw [hsb, path_fortran_loop st.mem _ sh strs idx hidx hnn hfl]
        have h4 : (st.mv self).view.itemsize * ((enc sh idx : Int) + 1) ≤
            (st.mv self).view.itemsize * prod sh :=
          Int.mul_le_mul_of_nonneg_left hlt (by omega)
        rw [Int.mul_add, Int.mul_one, Int.mul_comm (st.mv self).view.itemsize (prod sh), ← hlen] at h4
        have h5 : 0 ≤ (st.mv self).view.itemsize * (enc sh idx : Int) := Int.mul_nonneg (by omega) (by omega)
        exact rdBytes_rdBytes st.mem _ _ _ _ h5 (by omega)
    · refine ⟨M, ?_, h2, h3⟩
      rw [hto (some ['F']) 'F' rfl, hgo _ (by simpa using hc), h1]
  · rw [hto (some ['A']) 'A' rfl, hmem _ hc]
  · rw [hto (some ['A']) 'A' rfl, hgo _ hc, bufferToContiguous_A, hC]
  · simp [pyBufferToContiguous, hne']

/-- `memory_from_contiguous_copy` in order `'F'` (@3.14.7:888-946, @3.14.7:931-933): a new view over a new bytes
object with the shape and format of the source, Fortran strides and no suboffsets, holding each
item at its place in column-major order. `tolist(input) == tolist(output)`, the comment at @3.14.7:950-953.
`m` is the store including the new bytes. Hypotheses: the type invariants of a buffer. -/
def FromContigCopyF : Prop :=
  ∀ (st : St) (src : Buf) (sh strs : List Int) (f : List Char), src.shape = some sh →
    src.strides = some strs → src.format = some f →
    sh ≠ [] → sh.length = src.ndim → (∀ x ∈ sh, 0 ≤ x) → 0 < src.itemsize →
    src.len = prod sh * src.itemsize →
    let base : Int := st.mem.length
    let m := st.mem ++ List.replicate src.len.toNat 0
    let r := memoryFromContiguousCopy src 'F' st
    let i := st.mvs.length
    let v := (r.2.mv i).view
    r.1 = .ok i ∧ v.buf = base ∧ v.shape = some sh ∧ v.format = src.format ∧
      v.strides = some (fStrides src.itemsize sh) ∧ v.suboffsets = none ∧
      ∀ idx ∈ idxs sh, rdBytes r.2.mem (base + src.itemsize * enc sh idx) src.itemsize.toNat =
        rdBytes m (pathAddr m (toI idx) strs src.suboffsets src.buf) src.itemsize.toNat

theorem fromContigCopyF_proven : FromContigCopyF := by
  intro st src sh strs f hsh hst hf hne hn hnn hit hlen
  dsimp only
  have ⟨h1, hB⟩ := contigBytes_spec st src
  simp only [memoryFromContiguousCopy, M.bind_app]
  rcases hrr : contigBytes src st with ⟨r, s⟩
  rw [hrr] at h1 hB
  simp only at h1 hB
  subst h1
  simp only
  have ⟨ha, hA⟩ := mbufAddIncompleteView_added st.mbufs.length (s.mb st.mbufs.length).master src.ndim s
  have e0 : mbufAddIncompleteView st.mbufs.length none src.ndim s =
      mbufAddIncompleteView st.mbufs.length (some (s.mb st.mbufs.length).master) src.ndim s := rfl
  unfold contigFill
  simp only [M.bind_app, e0]
  rcases hr2 : mbufAddIncompleteView st.mbufs.length (some (s.mb st.mbufs.length).master) src.ndim s with
    ⟨r2, s3⟩
  rw [hr2] at ha hA
  simp only at ha hA
  subst ha
  have hmvs : s.mvs.length = st.mvs.length := by rw [hB.mvs]
  have hx : (s3.mv st.mvs.length).view =
      initSharedValues { ndim := src.ndim } (s.mb st.mbufs.length).master := by
    have := hA.new
    rw [hmvs] at this
    rw [this]
  have hmem3 : s3.mem = st.mem ++ List.replicate src.len.toNat 0 := by rw [hA.mem, hB.mem]
  have hlenN : (0 : Int) ≤ src.len := by
    rw [hlen]
    exact Int.mul_nonneg (prod_nonneg _ hnn) (by omega)
  obtain ⟨dest, hdest⟩ : ∃ d : Buf, d =
      { (s3.mv st.mvs.length).view with
        itemsize := src.itemsize, shape := some sh, strides := some (fStrides src.itemsize sh),
        suboffsets := none } := ⟨_, rfl⟩
  have hd : dest =
      { obj := some (.exp 1000000), buf := st.mem.length, len := src.len,
        itemsize := src.itemsize, readonly := (s.mb st.mbufs.length).master.readonly, ndim := src.ndim,
        format := some f, shape := some sh, strides := some (fStrides src.itemsize sh),
        suboffsets := none, hook := (s.mb st.mbufs.length).master.hook } := by
    rw [hdest, hx]
    simp [initSharedValues, hB.buf, hB.len, hB.format, hB.obj, hf, Int.toNat_of_nonneg hlenN]
  have hequiv := equiv_self src dest sh hsh hn (by rw [hd, hsh]) (by rw [hd]) (by rw [hd, hf]) (by rw [hd])
  have hdn : dest.ndim = src.ndim := by rw [hd]
  have hdi : dest.itemsize = src.itemsize := by rw [hd]
  have hdst : dest.strides = some (fStrides src.itemsize sh) := by rw [hd]
  have hn3 : st.mvs.length < s3.mvs.length := by rw [hA.len]; omega
  have hu : (!lastDimIsContiguous dest src) = false →
      (fStrides src.itemsize sh).getD (sh.length - 1) 0 = src.itemsize ∧
        LastOK src.itemsize sh strs src.suboffsets := by
    intro h
    refine ⟨?_, lastOK_of src dest sh strs hst hn h⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, lastDimIsContiguous, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨-, h1⟩, -⟩ := h
    rw [hdst, hdn, hdi, ← hn] at h1
    simpa using h1
  have hc := copyRec_seq src.itemsize (by omega) (!lastDimIsContiguous dest src)
    (st.mem ++ List.replicate src.len.toNat 0) sh hne hnn st.mem.length
    (fStrides src.itemsize sh) src.buf strs src.suboffsets (st.mem ++ List.replicate src.len.toNat 0) hu
  obtain ⟨L, hL⟩ : ∃ L, L = (idxs sh).map fun idx =>
      (pathAddr [] (toI idx) (fStrides src.itemsize sh) none (st.mem.length : Int),
       rdBytes (st.mem ++ List.replicate src.len.toNat 0)
         (pathAddr (st.mem ++ List.replicate src.len.toNat 0) (toI idx) strs src.suboffsets src.buf)
         src.itemsize.toNat) := ⟨_, rfl⟩
  rw [← hL] at hc
  have hcopy : copyBuffer (st.mem ++ List.replicate src.len.toNat 0) (st.mem ++ List.replicate src.len.toNat 0)
      dest src = .ok (writeSeq L (st.mem ++ List.replicate src.len.toNat 0)) := by
    simp only [copyBuffer, bind, Except.bind, hequiv, pure, Except.pure]
    rw [show dest.shape.getD [] = sh by rw [hd]; rfl,
      show dest.strides.getD [] = fStrides src.itemsize sh by rw [hd]; rfl,
      show dest.suboffsets = none by rw [hd],
      show dest.buf = st.mem.length by rw [hd],
      show dest.itemsize = src.itemsize by rw [hd], hst]
    simp only [Option.getD_some]
    rw [hc]
  have hcond : ¬ ((('F' : Char) = 'C') ∨ (('F' : Char) = 'A')) := by decide
  simp only [hmvs, hsh, Option.getD_some, hcond, ↓reduceIte, M.get, M.modify, M.lift, ← hdest,
    St.mem_setMv, hmem3, hcopy, M.pure_app]
  have hmv : ({ s3.setMv st.mvs.length { s3.mv st.mvs.length with view := dest, flags := initFlags dest } with
      mem := writeSeq L (st.mem ++ List.replicate src.len.toNat 0) } : St).mv
        st.mvs.length = { s3.mv st.mvs.length with view := dest, flags := initFlags dest } :=
    St.mv_setMv s3 _ _ hn3
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmv, hd]
  · rw [hmv, hd]
  · rw [hmv, hd, hf]
  · rw [hmv, hd]
  · rw [hmv, hd]
  · intro idx hidx
    rw [hL]
    exact fortran_writes src.itemsize hit sh hnn st.mem.length (by omega)
      (fun idx => rdBytes (st.mem ++ List.replicate src.len.toNat 0)
        (pathAddr (st.mem ++ List.replicate src.len.toNat 0) (toI idx) strs src.suboffsets src.buf)
        src.itemsize.toNat)
      (fun _ _ => rdBytes_length _ _ _) _ (by simp; omega) idx hidx

/-! ## A destination with suboffsets -/

theorem upto_pairwise (k i : Nat) : (upto k i).Pairwise (· < ·) := by
  induction k generalizing i with
  | zero => simp [upto]
  | succ k ih =>
    simp only [upto, List.pairwise_cons]
    refine ⟨fun a ha => ?_, ih _⟩
    have := (mem_upto _ _ _).1 ha
    omega

/-- `copy_base` through the scratch buffer writes each item at the address its pointer gives. The
pointers are read as the loop goes, so a write must not touch a later pointer. -/
theorem writeItems_sub (it : Nat) (ds : Int) (subs : Option (List Int)) (p : Int) (T : Nat → Int)
    (X : Nat → List Nat) (hX : ∀ j, (X j).length = it) (k i : Nat) (dm : Mem)
    (hT : ∀ j, i ≤ j → j < i + k → adjustPtr dm (p + ds * j) subs 0 = T j)
    (h0 : ∀ j, i ≤ j → j < i + k → 0 ≤ T j)
    (hc : ∀ a b, i ≤ a → a < b → b < i + k → 0 ≤ p + ds * b ∧
      (p + ds * b + 8 ≤ T a ∨ T a + it ≤ p + ds * b)) :
    writeItems it ds subs ((upto k i).map X) (p + ds * i) dm =
      writeSeq ((upto k i).map fun (j : Nat) => (T j, X j)) dm := by
  induction k generalizing i dm with
  | zero => rfl
  | succ k ih =>
    simp only [upto, List.map_cons, writeItems, writeSeq]
    have e : p + ds * (i : Int) + ds = p + ds * ((i + 1 : Nat) : Int) := by
      rw [Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_assoc]
    rw [e, hT i (by omega) (by omega)]
    apply ih
    · intro j h1 h2
      rw [adjustPtr_write dm (T i) (X i) _ subs (h0 i (by omega) (by omega)) (fun _ => by
        have := hc i j (by omega) (by omega) (by omega)
        rw [hX]
        exact this)]
      exact hT j (by omega) (by omega)
    · intro j h1 h2
      exact h0 j (by omega) (by omega)
    · intro a b h1 h2 h3
      exact hc a b (by omega) h2 (by omega)

/-- `m[s] = x` on a view with suboffsets, `copy_single` with a destination array of pointers
(`copy_base`, @3.14.7:345-371, reached with `mem != NULL` because `last_dim_is_contiguous`, @3.14.7:272-279, is
false there): each item of the source ends at the address its pointer gives, and the source may
have suboffsets too. Hypotheses: `equiv_structure` passed; the items land apart from each other and
from the pointers, inside the store, which is what a PIL array is. -/
def CopySingleSub : Prop :=
  ∀ (st : St) (self : Nat) (dest src : Buf) (n ds ss o : Int),
    baseInaccessible st self = false → equivStructure dest src = .ok () →
    dest.shape = some [n] → dest.strides = some [ds] → src.strides = some [ss] → dest.ndim = 1 →
    src.ndim = 1 → dest.suboffsets = some [o] → 0 ≤ o → 0 ≤ n → 0 < dest.itemsize →
    let cell (j : Nat) : Int := dest.buf + ds * j
    let T (j : Nat) : Int := adjustPtr st.mem (cell j) dest.suboffsets 0
    let it := dest.itemsize
    (∀ i j : Nat, (i : Int) < n → (j : Int) < n → 0 ≤ cell j ∧ (cell j + 8 ≤ T i ∨ T i + it ≤ cell j)) →
    (∀ i j : Nat, i < j → (j : Int) < n → T i + it ≤ T j ∨ T j + it ≤ T i) →
    (∀ j : Nat, (j : Int) < n → 0 ≤ T j ∧ T j + it ≤ st.mem.length) →
    let r := copySingle self dest src st
    r.1 = .ok () ∧ ∀ k : Nat, (k : Int) < n →
      rdBytes r.2.mem (T k) it.toNat =
        rdBytes st.mem (adjustPtr st.mem (src.buf + ss * k) src.suboffsets 0) it.toNat

theorem copySingleSub_proven : CopySingleSub := by
  intro st self dest src n ds ss o hl he hsh hst hsst hd1 hs1 hdsub ho hn hit
  dsimp only
  intro hcell hsep hb
  have hit' : ((dest.itemsize.toNat : Nat) : Int) = dest.itemsize := Int.toNat_of_nonneg (by omega)
  have hu : lastDimIsContiguous dest src = false := by
    have : haveSubInLast dest = true := by
      simp [haveSubInLast, hdsub, hd1, ho]
    simp [lastDimIsContiguous, this]
  obtain ⟨X, hX⟩ : ∃ X : Nat → List Nat, X = fun (j : Nat) =>
      rdBytes st.mem (adjustPtr st.mem (src.buf + ss * (j : Int)) src.suboffsets 0) dest.itemsize.toNat := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Nat → Int, T = fun (j : Nat) =>
      adjustPtr st.mem (dest.buf + ds * (j : Int)) dest.suboffsets 0 := ⟨_, rfl⟩
  have hXl : ∀ j, (X j).length = dest.itemsize.toNat := by
    intro j
    rw [hX]
    exact rdBytes_length _ _ _
  have hw := writeItems_sub dest.itemsize.toNat ds dest.suboffsets dest.buf T X hXl n.toNat 0 st.mem
    (fun j _ _ => by rw [hT]) (fun j _ h2 => by
      rw [hT]
      exact (hb j (by omega)).1)
    (fun a b _ h2 h3 => by
      have := hcell a b (by omega) (by omega)
      rw [hT, hit']
      exact this)
  have e0 : dest.buf + ds * ((0 : Nat) : Int) = dest.buf := by simp
  rw [e0] at hw
  have hbase : copyBase n dest.itemsize dest.buf ds dest.suboffsets src.buf ss src.suboffsets true st.mem st.mem =
      writeSeq ((upto n.toNat 0).map fun (j : Nat) => (T j, X j)) st.mem := by
    rw [← hw]
    simp only [copyBase, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readItems_eq]
    rw [walk_upto0, List.map_map, hX]
    rfl
  have hc : copySingle self dest src st =
      (.ok (), { st with mem := writeSeq ((upto n.toNat 0).map fun (j : Nat) => (T j, X j)) st.mem }) := by
    rw [← hbase]
    simp only [copySingle, M.bind_app, checkReleased_ok _ _ hl, M.lift, he, M.get, hsh, hst, hsst,
      Option.getD_some, List.getD_cons_zero, M.modify, hu, Bool.not_false]
  rw [hc]
  refine ⟨rfl, fun k hk => ?_⟩
  dsimp only
  have hr := writeSeq_read ((upto n.toNat 0).map fun (j : Nat) => (T j, X j)) st.mem dest.itemsize.toNat
    (by
      intro e he'
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 he'
      exact hXl a)
    (by
      intro e he'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he'
      have h1 := (mem_upto _ _ _).1 ha
      have := hb a (by omega)
      rw [hit']
      rw [hT]
      exact this)
    (by
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem (fun {a b} _ hb' hlt => ?_) (upto_pairwise n.toNat 0)
      have h1 := (mem_upto _ _ _).1 hb'
      have := hsep a b hlt (by omega)
      dsimp only
      rw [hit', hT]
      exact this)
    (T k, X k) (List.mem_map.2 ⟨k, (mem_upto _ _ _).2 ⟨by omega, by omega⟩, rfl⟩)
  subst hT hX
  exact hr

/-! ## The other arms of `pack_single` and `unpack_single` -/

theorem rdU_encLE (m : Mem) (p : Int) (n : Nat) (k : Nat) (hp : 0 ≤ p) (h : p + k ≤ m.length) :
    rdU (wrBytes m p (encLE n k)) p k = n % 256 ^ k := by
  unfold rdU
  rw [rd_after_write _ _ _ k (by simp [encLE_length]) hp h, decLE_encLE]

/-- `pack_single` then `unpack_single` for the formats other than the integers, for every memory
(`PackUnpackInt` is the integers): `?` stores the truth of the item, `c` one byte, `P` a pointer of 8
bytes, `d` a double exactly, and `f` and `e` read back the pattern they stored, which is a float
rounded to the format (`bytesobj-memoryview-float32-round-trip` is whether that is lossless). A
released view refuses to unpack, the `CHECK_RELEASED_AGAIN` of @3.14.7:1788. Hypotheses: the item's space
is in the store; a live view; for `?`, an item whose truth runs no Python code (`PackFailures`). -/
def PackUnpackOther : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int), 0 ≤ ptr → ptr + 8 ≤ st.mem.length →
    (baseInaccessible st self = true → ∀ f, unpackSingle self ptr f st = (.error releasedError, st)) ∧
    (baseInaccessible st self = false →
      (∀ item b, isTrue item st = (.ok b, st) → ∃ s, packSingle self ptr item ['?'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['?'] = .ok (.bool b)) ∧
      (∀ b, b < 256 → ∃ s, packSingle self ptr (.bytes [b]) ['c'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['c'] = .ok (.bytes [b])) ∧
      (∀ x : Nat, x < 2 ^ 64 → ∃ s, packSingle self ptr (.float x) ['d'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['d'] = .ok (.float x)) ∧
      (∀ x : Nat, ∃ s, packSingle self ptr (.float x) ['f'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['f'] = .ok (.float (widen32 (narrow32 x % 2 ^ 32)))) ∧
      (∀ x h : Nat, pack2 x = .ok h → ∃ s, packSingle self ptr (.float x) ['e'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['e'] = .ok (.float (unpack2 (h % 2 ^ 16)))) ∧
      (∀ p : Nat, p < 2 ^ 64 → ∃ s, packSingle self ptr (.int p) ['P'] st = (.ok (), s) ∧
        unpackRaw s.mem ptr ['P'] = .ok (.int p)))

theorem packUnpackOther_proven : PackUnpackOther := by
  intro st self ptr h0 h8
  refine ⟨fun hr f => ?_, fun hl => ?_⟩
  · simp only [unpackSingle, M.bind_app, checkReleased_err _ _ hr]
  have hc := checkReleased_ok st self hl
  have hk : ∀ k : Nat, k ≤ 8 → ptr + k ≤ st.mem.length := fun k hk => by omega
  refine ⟨fun item b hb => ?_, fun b hb => ?_, fun x hx => ?_, fun x => ?_, fun x h h2 => ?_, fun p hp => ?_⟩
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encInt (if b then 1 else 0) 1) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, hb, hc]
      rfl
    · have h1 := rdU_write st.mem ptr (if b then 1 else 0) 1 h0 (hk 1 (by omega))
      rw [rdU_one] at h1
      simp only [unpackRaw, cc, List.getD_cons_zero, unpackToBool]
      show Except.ok (Item.bool (rdByte (wrBytes st.mem ptr (encInt (if b then 1 else 0) 1)) ptr != 0)) = _
      rw [h1]
      cases b <;> decide
  · refine ⟨{ st with mem := wrBytes st.mem ptr [b] }, ?_, ?_⟩
    · rfl
    · have h1 := rdBytes_wrBytes st.mem ptr [b] h0 (by simpa using hk 1 (by omega))
      simp only [List.length_singleton, rdBytes] at h1
      have h2 : rdByte (wrBytes st.mem ptr [b]) ptr = b := by
        simpa using h1
      simp only [unpackRaw, cc, List.getD_cons_zero]
      show Except.ok (Item.bytes [rdByte (wrBytes st.mem ptr [b]) ptr]) = _
      rw [h2]
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encLE x 8) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, floatAsDouble, M.pure_app, hc]
      rfl
    · have h1 := rdU_encLE st.mem ptr x 8 h0 (hk 8 (by omega))
      rw [Nat.mod_eq_of_lt (by omega)] at h1
      show Except.ok (Item.float (rdU (wrBytes st.mem ptr (encLE x 8)) ptr 8)) = _
      rw [h1]
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encLE (narrow32 x) 4) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, floatAsDouble, M.pure_app, hc]
      rfl
    · have h1 := rdU_encLE st.mem ptr (narrow32 x) 4 h0 (hk 4 (by omega))
      show Except.ok (Item.float (widen32 (rdU (wrBytes st.mem ptr (encLE (narrow32 x) 4)) ptr 4))) = _
      rw [h1]
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encLE h 2) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, floatAsDouble, M.pure_app, hc,
        M.lift, h2]
      rfl
    · have h1 := rdU_encLE st.mem ptr h 2 h0 (hk 2 (by omega))
      show Except.ok (Item.float (unpack2 (rdU (wrBytes st.mem ptr (encLE h 2)) ptr 2))) = _
      rw [h1]
  · have hv : asVoidPtr (.int p) = .ok p := by
      simp [asVoidPtr, Obj.asLong?, asUnsignedLong, show ¬ ((p : Int) < 0) by omega]
      omega
    refine ⟨{ st with mem := wrBytes st.mem ptr (encInt p 8) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, M.lift, hv, M.pure_app, hc]
      rfl
    · have h1 := rdU_write st.mem ptr p 8 h0 (hk 8 (by omega))
      show Except.ok (Item.int (rdU (wrBytes st.mem ptr (encInt p 8)) ptr 8)) = _
      rw [h1]
      have e : ((p : Int) % (2 ^ (8 * 8) : Int)).toNat = p := by
        have : (p : Int) % (2 ^ (8 * 8) : Int) = p := Int.emod_eq_of_lt (by omega) (by omega)
        rw [this]
        rfl
      rw [e]

/-- `GetContiguousCopy` in Fortran order: a read request in order `'F'` on a view that is not
Fortran-contiguous gives a new view with Fortran strides holding the items in column-major order,
and the temporary view is dropped. Hypotheses: as `GetContiguousCopy`. -/
def GetContiguousCopyF : Prop :=
  ∀ (st : St) (self : Nat) (sh strs : List Int) (f : List Char), LiveView st self →
    let v := (st.mv self).view
    v.shape = some sh → v.strides = some strs → v.format = some f → sh ≠ [] → (∀ x ∈ sh, 0 ≤ x) →
    0 < v.itemsize → v.len = prod sh * v.itemsize → pyBufferIsContiguous v 'F' = false →
    let r := memoryViewGetContiguous (.view self) false 'F' st
    let i := st.mvs.length + 1
    let m := st.mem ++ List.replicate v.len.toNat 0
    r.1 = .ok i ∧ (r.2.mv i).view.shape = some sh ∧ (r.2.mv i).view.format = some f ∧
      (r.2.mv i).view.strides = some (fStrides v.itemsize sh) ∧ (r.2.mv i).view.suboffsets = none ∧
      (∀ idx ∈ idxs sh, rdBytes r.2.mem ((st.mem.length : Int) + v.itemsize * enc sh idx) v.itemsize.toNat =
        rdBytes m (pathAddr m (toI idx) strs v.suboffsets v.buf) v.itemsize.toNat)

theorem getContiguousCopyF_proven : GetContiguousCopyF := by
  intro st self sh strs f hL
  dsimp only
  intro hsh hst hf hne hnn hit hlen hc
  have hview := viewCopy_full _ hL.full
  have hrank : sh.length = (st.mv self).view.ndim := by
    rcases hL.full.arrays with ⟨-, h4, -⟩ | ⟨a, b, -, h4, -, h5, -⟩
    · rw [hsh] at h4
      cases h4
    · rw [hsh] at h5
      simp only [Option.some.injEq] at h5
      subst h5
      exact h4
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st hL.small
  rw [hview] at hA
  have e : memoryViewFromObject (.view self) st =
      mbufAddView (st.mv self).mbuf (some (st.mv self).view) st := by
    simp only [memoryViewFromObject, memoryViewFromObjectAndFlags, M.bind_app,
      checkReleased_ok _ _ hL.live, checkRestricted_ok _ _ hL.unres, M.get]
  rcases hrr : mbufAddView (st.mv self).mbuf (some (st.mv self).view) st with ⟨r1, st1⟩
  rw [hrr] at hr1 hA e
  simp only at hr1 hA
  subst hr1
  have hnew : (st1.mv st.mvs.length).view = (st.mv self).view := by rw [hA.new]
  have hcopy := fromContigCopyF_proven st1 (st.mv self).view sh strs f hsh hst hf hne hrank hnn hit hlen
  dsimp only at hcopy
  rcases hrc : memoryFromContiguousCopy (st.mv self).view 'F' st1 with ⟨r2, s2⟩
  rw [hrc] at hcopy
  simp only at hcopy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcopy
  subst h1
  rcases hd : memoryDealloc st.mvs.length s2 with ⟨r3, s3⟩
  have hok := memoryDealloc_ok st.mvs.length s2
  rw [hd] at hok
  simp only at hok
  subst hok
  have hmono : Mono s2 s3 := by
    have h9 := deallocMono st.mvs.length s2
    rw [hd] at h9
    exact h9
  have hlen1 : st1.mvs.length = st.mvs.length + 1 := hA.len
  have hg : memoryViewGetContiguous (.view self) false 'F' st = (.ok (st.mvs.length + 1), s3) := by
    simp only [memoryViewGetContiguous, M.bind_app, e, M.get, hnew, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, hc, hrc, hd, M.pure_app, hlen1]
  rw [hg]
  simp only
  rw [hlen1] at h3 h4 h5 h6
  rw [hA.mem] at h7
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmono.view, h3]
  · rw [hmono.view, h4, hf]
  · rw [hmono.view, h5]
  · rw [hmono.view, h6]
  · intro idx hidx
    rw [hmono.mem]
    exact h7 idx hidx

end PyLean.BytesObj.Mem
