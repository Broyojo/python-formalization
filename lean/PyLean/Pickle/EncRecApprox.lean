import PyLean.Pickle.EncRec

/-!
Each bounded encoder of `EncRec.lean` computes what its frames-free twin in `Enc.lean`
computes, or raises its `RecursionError`: `Approx r m m'` says that from every state `m` ends as
`m'` does, or with the exception `r`.
-/

namespace PyLean.Pickle

open PyLean

def Approx (r : PyExc) {α : Type} (m m' : EncM α) : Prop := ∀ s, m s = m' s ∨ m s = .error r

variable {r : PyExc}

theorem approx_refl {α : Type} (m : EncM α) : Approx r m m := fun _ => .inl rfl

theorem approx_bind {α β : Type} {m m' : EncM α} {k k' : α → EncM β} (h1 : Approx r m m')
    (h2 : ∀ a, Approx r (k a) (k' a)) : Approx r (m >>= k) (m' >>= k') := by
  intro s
  show (StateT.bind m k) s = (StateT.bind m' k') s ∨ (StateT.bind m k) s = .error r
  simp only [StateT.bind, bind, Except.bind]
  rcases h1 s with h | h
  · rw [h]
    cases m' s with
    | error e => exact .inl rfl
    | ok v => exact h2 v.1 v.2
  · rw [h]; exact .inr rfl

theorem approx_bind_pure {α β : Type} {m : EncM α} {a : α} {k : α → EncM β} {m'' : EncM β}
    (h1 : Approx r m (pure a)) (h2 : Approx r (k a) m'') : Approx r (m >>= k) m'' := by
  intro s
  show (StateT.bind m k) s = m'' s ∨ (StateT.bind m k) s = .error r
  simp only [StateT.bind, bind, Except.bind]
  rcases h1 s with h | h
  · rw [h]; exact h2 s
  · rw [h]; exact .inr rfl

theorem approx_pyCall {α : Type} {b : Nat} {k : Nat → EncM α} {m' : EncM α}
    (h : ∀ b', Approx recPy (k b') m') : Approx recPy (pyCall b k) m' := by
  unfold pyCall
  split
  · intro s; exact .inr rfl
  · exact h _

theorem approx_cEnter {c : Nat} {k : Nat → EncM Unit} {m' : EncM Unit}
    (h : ∀ c', Approx recC (k c') m') : Approx recC (cEnter c k) m' := by
  unfold cEnter
  split
  · intro s; exact .inr rfl
  · exact h _

theorem approx_ite {α : Type} {c : Prop} [Decidable c] {a b a' b' : EncM α}
    (h1 : c → Approx r a a') (h2 : ¬ c → Approx r b b') :
    Approx r (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem approx_opt {α : Type} {o : Option Nat} {f f' : Nat → EncM α} {g g' : EncM α}
    (h1 : ∀ i, Approx r (f i) (f' i)) (h2 : Approx r g g') :
    Approx r (match o with | some i => f i | none => g) (match o with | some i => f' i | none => g') := by
  cases o with
  | some i => exact h1 i
  | none => exact h2

/-! ## Python -/

theorem ap_pyW (b : Nat) (d : Bytes) : Approx recPy (pyW b d) (wr d) :=
  approx_pyCall fun _ => approx_refl _

theorem ap_commit (b : Nat) : Approx recPy (pyCommitR b) (emit .boundary) :=
  approx_pyCall fun _ => approx_refl _

theorem ap_pers (b : Nat) : Approx recPy (pyPersR b) (pure ()) :=
  approx_pyCall fun _ => approx_refl _

theorem ap_large (b p : Nat) (h d : Bytes) : Approx recPy (pyLargeR b p h d) (emit (.large h d)) :=
  approx_pyCall fun _ => by
    by_cases hp : p ≥ 4
    · rw [if_pos hp]; exact approx_pyCall fun _ => approx_refl _
    · rw [if_neg hp]; exact approx_refl _

theorem ap_get (b p i : Nat) : Approx recPy (pyGetR b p i) (liftPy (pyGet p i)) :=
  approx_pyCall fun _ => approx_refl _

theorem ap_getw (b p i : Nat) :
    Approx recPy (pyGetR b p i >>= fun d => pyW b d) (liftPy (pyGet p i) >>= fun d => wr d) :=
  approx_bind (ap_get b p i) fun d => ap_pyW b d

theorem ap_memoize (b p : Nat) (o : Oid) : Approx recPy (pyMemoizeR b p o) (pyMemoize p o) :=
  approx_pyCall fun _ => approx_bind (approx_refl _) fun _ =>
    approx_bind (approx_pyCall fun _ => approx_refl _) fun d =>
      approx_bind (ap_pyW _ d) fun _ => approx_refl _

theorem ap_optWr (b : Nat) (c : Prop) [Decidable c] (d : Bytes) :
    Approx recPy (optWrR b c d) (optWr c d) :=
  approx_ite (fun _ => ap_pyW b d) (fun _ => approx_refl _)

theorem ap_emptyOp (b p : Nat) (e o : UInt8) : Approx recPy (pyEmptyOpR b p e o) (pyEmptyOp p e o) :=
  approx_ite (fun _ => ap_pyW _ _) (fun _ => ap_pyW _ _)

theorem ap_batchStep (b p n i : Nat) {it it' : EncM Unit} (h : Approx recPy it it') (one many : UInt8) :
    Approx recPy (pyBatchStepR b p n i it one many) (pyBatchStep p n i it' one many) :=
  approx_ite (fun _ => approx_bind h fun _ => ap_pyW _ _)
    (fun _ => approx_bind (ap_optWr _ _ _) fun _ => approx_bind h fun _ => ap_optWr _ _ _)

theorem ap_addStep (b n i : Nat) {it it' : EncM Unit} (h : Approx recPy it it') :
    Approx recPy (addStepR b n i it) (addStep n i it') :=
  approx_bind (ap_optWr _ _ _) fun _ => approx_bind h fun _ => ap_optWr _ _ _

theorem ap_saveLong (b p : Nat) (i : Int) :
    Approx recPy (pySaveLongR b p i) (liftPy (pySaveLong p i) >>= fun d => wr d) := by
  have h1 : Approx recPy (pySaveLongR.pyEncodeLongR b p i) (pure ()) := by
    unfold pySaveLongR.pyEncodeLongR
    split
    · exact approx_pyCall fun _ => approx_refl _
    · exact approx_refl _
  exact approx_bind_pure h1 (approx_bind (approx_refl _) fun d => ap_pyW b d)

theorem ap_lift_large (b p : Nat) (a : Py Bytes) (op : UInt8) (d : Bytes) :
    Approx recPy (liftPy a >>= fun x => pyLargeR b p (op :: x) d) (liftPy a >>= fun x => emit (.large (op :: x) d)) :=
  approx_bind (approx_refl _) fun _ => ap_large _ _ _ _

theorem ap_lift_w (b : Nat) (a : Py Bytes) (op : UInt8) (d : Bytes) :
    Approx recPy (liftPy a >>= fun x => pyW b (op :: x ++ d)) (liftPy a >>= fun x => wr (op :: x ++ d)) :=
  approx_bind (approx_refl _) fun _ => ap_pyW _ _

theorem ap_strData (b p : Nat) (d : Bytes) : Approx recPy (pyStrDataR b p d) (pyStrData p d) :=
  approx_ite (fun _ => ap_pyW _ _) fun _ => approx_ite (fun _ => ap_large _ _ _ _) fun _ =>
    approx_ite (fun _ => ap_lift_large _ _ _ _ _) (fun _ => ap_lift_w _ _ _ _)

theorem ap_strBody (b p : Nat) (s : List Nat) : Approx recPy (pyStrBodyR b p s) (pyStrBody p s) :=
  approx_ite (fun _ => ap_strData _ _ _) (fun _ => ap_pyW _ _)

theorem ap_saveStr (b p : Nat) (o : Oid) (s : List Nat) : Approx recPy (pySaveStrR b p o s) (pySaveStr p o s) :=
  approx_bind (ap_strBody _ _ _) fun _ => ap_memoize _ _ _

/-- The frames-free start of `save`: boundary, memo. -/
def uHead (p : Nat) (o : Oid) (body : EncM Unit) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (pyGet p i))
  | none => body

theorem ap_head (b p : Nat) (o : Oid) {body body' : EncM Unit} (h : Approx recPy body body') :
    Approx recPy (pySaveHead b p o body) (uHead p o body') :=
  approx_bind (ap_commit b) fun _ => approx_bind_pure (ap_pers b) <|
    approx_bind (approx_refl _) fun v => approx_opt (fun i => ap_getw b p i) h

theorem ap_strObj (b p : Nat) (o : Oid) (s : List Nat) :
    Approx recPy (pySaveStrObjR b p o s) (pySaveStrObj p o s) :=
  approx_pyCall fun _ => ap_head _ _ _ (approx_pyCall fun _ => ap_saveStr _ _ _ _)

theorem ap_globalBody (b p : Nat) (g : Glob) :
    Approx recPy (pySaveGlobalBodyR b p g) (do pyGlobalRef p g; pyMemoize p (.glob g)) := by
  have h : Approx recPy (pySaveGlobalBodyR.pyGlobalRefR b p g) (pyGlobalRef p g) := by
    unfold pySaveGlobalBodyR.pyGlobalRefR pyGlobalRef
    split
    · exact approx_bind (ap_strObj _ _ _ _) fun _ => approx_bind (ap_strObj _ _ _ _) fun _ => ap_pyW _ _
    · exact approx_pyCall fun _ => approx_bind (ap_pyW _ _) fun _ => ap_pyW _ _
  exact approx_bind_pure (approx_pyCall fun _ => approx_pyCall fun _ => approx_refl _) <|
    approx_bind h fun _ => ap_memoize _ _ _

theorem ap_global (b p : Nat) (g : Glob) : Approx recPy (pySaveGlobalR b p g) (pySaveGlobal p g) := by
  refine approx_pyCall fun _ => ap_head _ _ _ ?_
  by_cases hg : g = .codecsEncode
  · rw [if_pos hg]; exact approx_pyCall fun _ => ap_globalBody _ _ _
  · rw [if_neg hg]; exact approx_pyCall fun _ => approx_pyCall fun _ => ap_globalBody _ _ _

theorem ap_tupleWith (b p n : Nat) (o : Oid) {e e' : EncM Unit} (h : Approx recPy e e') :
    Approx recPy (pyTupleWithR b p o n e) (pyTupleWith p o n e') := by
  unfold pyTupleWithR pyTupleWith
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
    exact approx_ite (fun _ => ap_pyW _ _) (fun _ => ap_pyW _ _)
  rw [if_neg h0, if_neg h0]
  by_cases h3 : n ≤ 3 ∧ p ≥ 2
  · rw [if_pos h3, if_pos h3]
    refine approx_bind h fun _ => approx_bind (approx_refl _) fun v => approx_opt (fun i => ?_) ?_
    · exact approx_bind (ap_get _ _ _) fun _ => ap_pyW _ _
    · exact approx_bind (ap_pyW _ _) fun _ => ap_memoize _ _ _
  · rw [if_neg h3, if_neg h3]
    refine approx_bind (ap_pyW _ _) fun _ => approx_bind h fun _ =>
      approx_bind (approx_refl _) fun v => approx_opt (fun i => ?_) ?_
    · exact approx_ite (fun _ => approx_bind (ap_get _ _ _) fun _ => ap_pyW _ _)
        (fun _ => approx_bind (ap_get _ _ _) fun _ => ap_pyW _ _)
    · exact approx_bind (ap_pyW _ _) fun _ => ap_memoize _ _ _

theorem ap_tupleObj (b p n : Nat) (o : Oid) {e : Nat → EncM Unit} {e' : EncM Unit}
    (h : ∀ b', Approx recPy (e b') e') : Approx recPy (pyTupleObjR b p o n e) (pyTupleObj p o n e') :=
  approx_pyCall fun _ => ap_head _ _ _ (approx_pyCall fun _ => ap_tupleWith _ _ _ _ (h _))

theorem ap_reduce (b p : Nat) (o : Oid) (g : Glob) {a : Nat → EncM Unit} {a' : EncM Unit}
    (h : ∀ b', Approx recPy (a b') a') : Approx recPy (pyReduceWithR b p o g a) (pyReduceWith p o g a') :=
  approx_pyCall fun _ => approx_bind (ap_global _ _ _) fun _ => approx_bind (h _) fun _ =>
    approx_bind (ap_pyW _ _) fun _ => approx_bind (approx_refl _) fun v =>
      approx_opt (fun i => approx_bind (ap_get _ _ _) fun _ => ap_pyW _ _) (ap_memoize _ _ _)

theorem ap_bytesData (b p : Nat) (d : Bytes) : Approx recPy (pySaveBytesDataR b p d) (pySaveBytesData p d) :=
  approx_ite (fun _ => ap_pyW _ _) fun _ => approx_ite (fun _ => ap_large _ _ _ _) fun _ =>
    approx_ite (fun _ => ap_lift_large _ _ _ _ _) (fun _ => ap_lift_w _ _ _ _)

theorem ap_bytearrayData (b p : Nat) (d : Bytes) :
    Approx recPy (pySaveBytearrayDataR b p d) (pySaveBytearrayData d) :=
  approx_ite (fun _ => ap_large _ _ _ _) (fun _ => ap_pyW _ _)

theorem ap_bytesObj (b p : Nat) (o : Oid) (d : Bytes) :
    Approx recPy (pySaveBytesObjR b p o d) (pySaveBytesObj p o d) := by
  refine approx_pyCall fun _ => ap_head _ _ _ (approx_pyCall fun _ => ?_)
  refine approx_ite (fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => ?_)
  · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ => approx_refl _
  · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ =>
      approx_bind (ap_strObj _ _ _ _) fun _ => ap_strObj _ _ _ _
  · exact approx_bind (approx_pyCall fun _ => ap_bytesData _ _ _) fun _ => ap_memoize _ _ _

theorem ap_bytearrayObj (b p : Nat) (o : Oid) (d : Bytes) :
    Approx recPy (pySaveBytearrayObjR b p o d) (pySaveBytearrayObj p o d) := by
  refine approx_pyCall fun _ => ap_head _ _ _ (approx_pyCall fun _ => ?_)
  refine approx_ite (fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => ?_)
  · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ => approx_refl _
  · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ => ap_bytesObj _ _ _ _
  · exact approx_bind (approx_pyCall fun _ => ap_bytearrayData _ _ _) fun _ => ap_memoize _ _ _

theorem ap_listWith (b p : Nat) (o : Oid) {it : Nat → EncM Unit} {it' : EncM Unit}
    (h : ∀ b', Approx recPy (it b') it') : Approx recPy (pyListWithR b p o it) (pyListWith p o it') :=
  approx_bind (ap_emptyOp _ _ _ _) fun _ => approx_bind (ap_memoize _ _ _) fun _ => approx_pyCall h

theorem ap_tmpList (b p : Nat) (o : Oid) (xs : List PV) {it : Nat → EncM Unit} {it' : EncM Unit}
    (h : ∀ b', Approx recPy (it b') it') :
    Approx recPy (pyTmpListR b p o xs it) (do emit .boundary; pyListWith p o it') :=
  approx_pyCall fun _ => approx_bind (ap_commit _) fun _ => approx_bind_pure (ap_pers _) <|
    approx_pyCall fun _ => ap_listWith _ _ _ h

mutual
theorem ap_save (b p : Nat) : (x : PV) → Approx recPy (pySaveR b p x) (pySave p x)
  | .none => by
    rw [pySaveR, pySave]
    exact approx_pyCall fun _ => approx_bind (ap_commit _) fun _ => approx_bind_pure (ap_pers _) <|
      approx_pyCall fun _ => ap_pyW _ _
  | .bool v => by
    rw [pySaveR, pySave]
    exact approx_pyCall fun _ => approx_bind (ap_commit _) fun _ => approx_bind_pure (ap_pers _) <|
      approx_pyCall fun _ => approx_ite (fun _ => ap_pyW _ _) (fun _ => ap_pyW _ _)
  | .int i => by
    rw [pySaveR, pySave]
    exact approx_pyCall fun _ => approx_bind (ap_commit _) fun _ => approx_bind_pure (ap_pers _) <|
      approx_pyCall fun _ => ap_saveLong _ _ _
  | .str o s => by rw [pySaveR, pySave]; exact ap_strObj _ _ _ _
  | .bytes o d => by rw [pySaveR, pySave]; exact ap_bytesObj _ _ _ _
  | .bytearray o d => by rw [pySaveR, pySave]; exact ap_bytearrayObj _ _ _ _
  | .tuple o xs => by
    rw [pySaveR, pySave]
    exact ap_tupleObj _ _ _ _ fun _ => ap_elems _ _ xs
  | .list o xs => by
    rw [pySaveR, pySave]
    exact approx_pyCall fun _ => ap_head _ _ _ <| approx_pyCall fun _ =>
      ap_listWith _ _ _ fun _ => ap_appends _ _ _ _ xs
  | .dict o kvs => by
    rw [pySaveR, pySave]
    exact approx_pyCall fun _ => ap_head _ _ _ <| approx_pyCall fun _ =>
      approx_bind (ap_emptyOp _ _ _ _) fun _ => approx_bind (ap_memoize _ _ _) fun _ =>
        approx_pyCall fun _ => ap_setitems _ _ _ _ kvs
  | .set o xs => by
    rw [pySaveR, pySave]
    refine approx_pyCall fun _ => ap_head _ _ _ <| approx_pyCall fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)
    · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ =>
        ap_tmpList _ _ _ _ fun _ => ap_appends _ _ _ _ xs
    · exact approx_bind (ap_pyW _ _) fun _ => approx_bind (ap_memoize _ _ _) fun _ => ap_additems _ _ _ _ xs
  | .frozenset o xs => by
    rw [pySaveR, pySave]
    refine approx_pyCall fun _ => ap_head _ _ _ <| approx_pyCall fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)
    · exact ap_reduce _ _ _ _ fun _ => ap_tupleObj _ _ _ _ fun _ =>
        ap_tmpList _ _ _ _ fun _ => ap_appends _ _ _ _ xs
    · exact approx_bind (ap_pyW _ _) fun _ => approx_bind (ap_elems _ _ xs) fun _ =>
        approx_bind (approx_refl _) fun v => approx_opt
          (fun i => approx_bind (ap_get _ _ _) fun _ => ap_pyW _ _)
          (approx_bind (ap_pyW _ _) fun _ => ap_memoize _ _ _)

theorem ap_elems (b p : Nat) : (xs : List PV) → Approx recPy (pySaveElemsR b p xs) (pySaveElems p xs)
  | [] => by rw [pySaveElemsR, pySaveElems]; exact approx_refl _
  | x :: xs => by
    rw [pySaveElemsR, pySaveElems]
    exact approx_bind (ap_save b p x) fun _ => ap_elems b p xs

theorem ap_appends (b p n i : Nat) : (xs : List PV) → Approx recPy (pyAppendsR b p n i xs) (pyAppends p n i xs)
  | [] => by rw [pyAppendsR, pyAppends]; exact approx_refl _
  | x :: xs => by
    rw [pyAppendsR, pyAppends]
    exact approx_bind (ap_batchStep _ _ _ _ (ap_save b p x) _ _) fun _ => ap_appends b p n (i + 1) xs

theorem ap_setitems (b p n i : Nat) :
    (kvs : List (PV × PV)) → Approx recPy (pySetitemsR b p n i kvs) (pySetitems p n i kvs)
  | [] => by rw [pySetitemsR, pySetitems]; exact approx_refl _
  | (k, v) :: kvs => by
    rw [pySetitemsR, pySetitems]
    exact approx_bind (ap_batchStep _ _ _ _ (approx_bind (ap_save b p k) fun _ => ap_save b p v) _ _)
      fun _ => ap_setitems b p n (i + 1) kvs

theorem ap_additems (b p n i : Nat) : (xs : List PV) → Approx recPy (pyAdditemsR b p n i xs) (pyAdditems p n i xs)
  | [] => by rw [pyAdditemsR, pyAdditems]; exact approx_refl _
  | x :: xs => by
    rw [pyAdditemsR, pyAdditems]
    exact approx_bind (ap_addStep _ _ _ (ap_save b p x)) fun _ => ap_additems b p n (i + 1) xs
end

theorem ap_body (b p : Nat) (x : PV) : Approx recPy (pyBodyR b p x) (pyBody p x) := by
  have tail : Approx recPy
      (do pySaveR b p x; pyW b [oSTOP]; pyCall b fun b' => if p ≥ 4 then pyCall b' (fun _ => emit .finish) else emit .finish)
      (do pySave p x; wr [oSTOP]; emit .finish) := by
    refine approx_bind (ap_save _ _ _) fun _ => approx_bind (ap_pyW _ _) fun _ => approx_pyCall fun _ => ?_
    split
    · exact approx_pyCall fun _ => approx_refl _
    · exact approx_refl _
  unfold pyBodyR pyBody
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;> simp only [h2, h4, if_true, if_false] at tail ⊢ <;>
    first
    | exact approx_bind (ap_pyW _ _) fun _ => approx_bind (approx_pyCall fun _ => approx_refl _) fun _ => tail
    | exact approx_bind (ap_pyW _ _) fun _ => tail
    | exact approx_bind (approx_pyCall fun _ => approx_refl _) fun _ => tail
    | exact tail
    | omega

/-! ## C -/

theorem ac_global (c p : Nat) (g : Glob) : Approx recC (cSaveGlobalR c p g) (cSaveGlobal p g) :=
  approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
    approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ => approx_refl _)

theorem ac_tupleWith (p n : Nat) (o : Oid) {e e' : EncM Unit} (h : Approx recC e e') :
    Approx recC (cTupleWith p o n e) (cTupleWith p o n e') := by
  unfold cTupleWith
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]; exact approx_refl _
  rw [if_neg h0, if_neg h0]
  by_cases h3 : n ≤ 3 ∧ p ≥ 2
  · rw [if_pos h3, if_pos h3]; exact approx_bind h fun _ => approx_refl _
  · rw [if_neg h3, if_neg h3]
    exact approx_bind (approx_refl _) fun _ => approx_bind h fun _ => approx_refl _

theorem ac_tupleObj (c p n : Nat) (o : Oid) {e : Nat → EncM Unit} {e' : EncM Unit}
    (h : ∀ c', Approx recC (e c') e') : Approx recC (cTupleObjR c p o n e) (cTupleObj p o n e') :=
  approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
    approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ => ac_tupleWith _ _ _ (h _))

theorem ac_reduce (c p : Nat) (o : Oid) (g : Glob) {a a' : EncM Unit} (h : Approx recC a a') :
    Approx recC (cReduceWithR c p o g a) (cReduceWith p o g a') :=
  approx_bind (ac_global _ _ _) fun _ => approx_bind h fun _ => approx_refl _

theorem ac_bytesObj (c p : Nat) (o : Oid) (d : Bytes) :
    Approx recC (cSaveBytesObjR c p o d) (cSaveBytesObj p o d) := by
  refine approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
    approx_opt (fun _ => approx_refl _) ?_
  refine approx_ite (fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => approx_refl _)
  · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => approx_refl _)
  · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => approx_refl _)

theorem ac_bytearrayObj (c p : Nat) (o : Oid) (d : Bytes) :
    Approx recC (cSaveBytearrayObjR c p o d) (cSaveBytearrayObj p o d) := by
  refine approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
    approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ => ?_)
  refine approx_ite (fun _ => approx_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => approx_refl _)
  · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => approx_refl _)
  · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => ac_bytesObj _ _ _ _)

theorem ac_listWith (p n : Nat) (o : Oid) {it it' : EncM Unit} (h : Approx recC it it') :
    Approx recC (cListWith p o n it) (cListWith p o n it') := by
  unfold cListWith
  exact approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun _ =>
    approx_ite (fun _ => h) (fun _ => approx_refl _)

theorem ac_tmpList (c p n : Nat) (o : Oid) {it : Nat → EncM Unit} {it' : EncM Unit}
    (h : ∀ c', Approx recC (it c') it') :
    Approx recC (cTmpListR c p o n it) (do emit .boundary; cListWith p o n it') :=
  approx_bind (approx_refl _) fun _ => approx_cEnter fun _ => ac_listWith _ _ _ (approx_cEnter h)

theorem ac_batchStep (p n i : Nat) {it it' : EncM Unit} (h : Approx recC it it') (one many : UInt8) :
    Approx recC (cBatchStep p n i it one many) (cBatchStep p n i it' one many) := by
  unfold cBatchStep
  exact approx_ite (fun _ => approx_bind h fun _ => approx_refl _) fun _ =>
    approx_ite (fun _ => approx_bind h fun _ => approx_refl _)
      (fun _ => approx_bind (approx_refl _) fun _ => approx_bind h fun _ => approx_refl _)

theorem ac_addStep (n i : Nat) {it it' : EncM Unit} (h : Approx recC it it') :
    Approx recC (addStep n i it) (addStep n i it') :=
  approx_bind (approx_refl _) fun _ => approx_bind h fun _ => approx_refl _

mutual
theorem ac_save (c p : Nat) : (x : PV) → Approx recC (cSaveR c p x) (cSave p x)
  | .none => by rw [cSaveR, cSave]; exact approx_refl _
  | .bool v => by rw [cSaveR, cSave]; exact approx_refl _
  | .int i => by rw [cSaveR, cSave]; exact approx_refl _
  | .str o s => by rw [cSaveR, cSave]; exact approx_refl _
  | .bytes o d => by rw [cSaveR, cSave]; exact ac_bytesObj _ _ _ _
  | .bytearray o d => by rw [cSaveR, cSave]; exact ac_bytearrayObj _ _ _ _
  | .tuple o xs => by
    rw [cSaveR, cSave]
    exact ac_tupleObj _ _ _ _ fun _ => ac_elems _ _ xs
  | .list o xs => by
    rw [cSaveR, cSave]
    exact approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
      approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ =>
        ac_listWith _ _ _ (approx_cEnter fun _ => ac_appends _ _ _ _ xs))
  | .dict o kvs => by
    rw [cSaveR, cSave]
    exact approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
      approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ =>
        approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun _ =>
          approx_ite (fun _ => approx_cEnter fun _ => ac_setitems _ _ _ _ kvs) (fun _ => approx_refl _))
  | .set o xs => by
    rw [cSaveR, cSave]
    refine approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
      approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ => approx_ite (fun _ => ?_) (fun _ => ?_))
    · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => ac_tmpList _ _ _ _ fun _ => ac_appends _ _ _ _ xs)
    · exact approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun _ =>
        approx_ite (fun _ => ac_additems _ _ _ _ xs) (fun _ => approx_refl _)
  | .frozenset o xs => by
    rw [cSaveR, cSave]
    refine approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun v =>
      approx_opt (fun _ => approx_refl _) (approx_cEnter fun _ => approx_ite (fun _ => ?_) (fun _ => ?_))
    · exact ac_reduce _ _ _ _ (ac_tupleObj _ _ _ _ fun _ => ac_tmpList _ _ _ _ fun _ => ac_appends _ _ _ _ xs)
    · exact approx_bind (approx_refl _) fun _ => approx_bind (ac_elems _ _ xs) fun _ =>
        approx_bind (approx_refl _) fun v => approx_opt (fun _ => approx_refl _) (approx_refl _)

theorem ac_elems (c p : Nat) : (xs : List PV) → Approx recC (cSaveElemsR c p xs) (cSaveElems p xs)
  | [] => by rw [cSaveElemsR, cSaveElems]; exact approx_refl _
  | x :: xs => by
    rw [cSaveElemsR, cSaveElems]
    exact approx_bind (ac_save c p x) fun _ => ac_elems c p xs

theorem ac_appends (c p n i : Nat) : (xs : List PV) → Approx recC (cAppendsR c p n i xs) (cAppends p n i xs)
  | [] => by rw [cAppendsR, cAppends]; exact approx_refl _
  | x :: xs => by
    rw [cAppendsR, cAppends]
    exact approx_bind (ac_batchStep _ _ _ (ac_save c p x) _ _) fun _ => ac_appends c p n (i + 1) xs

theorem ac_setitems (c p n i : Nat) :
    (kvs : List (PV × PV)) → Approx recC (cSetitemsR c p n i kvs) (cSetitems p n i kvs)
  | [] => by rw [cSetitemsR, cSetitems]; exact approx_refl _
  | (k, v) :: kvs => by
    rw [cSetitemsR, cSetitems]
    exact approx_bind (ac_batchStep _ _ _ (approx_bind (ac_save c p k) fun _ => ac_save c p v) _ _)
      fun _ => ac_setitems c p n (i + 1) kvs

theorem ac_additems (c p n i : Nat) : (xs : List PV) → Approx recC (cAdditemsR c p n i xs) (cAdditems p n i xs)
  | [] => by rw [cAdditemsR, cAdditems]; exact approx_refl _
  | x :: xs => by
    rw [cAdditemsR, cAdditems]
    exact approx_bind (ac_addStep _ _ (ac_save c p x)) fun _ => ac_additems c p n (i + 1) xs
end

theorem ac_body (c p : Nat) (x : PV) : Approx recC (cBodyR c p x) (cBody p x) := by
  have tail : Approx recC (do cSaveR c p x; wr [oSTOP]; emit .finish) (do cSave p x; wr [oSTOP]; emit .finish) :=
    approx_bind (ac_save _ _ _) fun _ => approx_refl _
  unfold cBodyR cBody
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;> simp only [h2, h4, if_true, if_false] <;>
    first
    | exact approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun _ => tail
    | exact approx_bind (approx_refl _) fun _ => tail
    | exact tail
    | omega

end PyLean.Pickle
