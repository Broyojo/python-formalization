import PyLean.Pickle.EncRecApprox

/-!
With enough room the bounded encoders are their frames-free twins exactly: C with
`4 * dep x + 4` levels of stack room, Python with `10 * dep x + 16` frames, where `dep` is the
container nesting depth. Each level costs C at most four guards (a set below protocol 4: its own,
the argument tuple's, the temporary list's two) and Python at most ten frames (the same path:
`save`, `save_set`, `save_reduce`, `save`, `save_tuple`, `save`, `save_list`, `_batch_appends`, with
`save(set)` for the callable alongside); a leaf takes at most 3 levels (a `bytearray` below
protocol 3) and 15 frames.
-/

namespace PyLean.Pickle

open PyLean

mutual
def PV.dep : PV → Nat
  | .tuple _ xs | .list _ xs | .set _ xs | .frozenset _ xs => PV.depL xs + 1
  | .dict _ kvs => PV.depP kvs + 1
  | _ => 0
def PV.depL : List PV → Nat
  | [] => 0
  | x :: xs => max (PV.dep x) (PV.depL xs)
def PV.depP : List (PV × PV) → Nat
  | [] => 0
  | (k, v) :: kvs => max (max (PV.dep k) (PV.dep v)) (PV.depP kvs)
end

theorem eq_bind {α β : Type} {m m' : EncM α} {k k' : α → EncM β} (h1 : m = m') (h2 : ∀ a, k a = k' a) :
    (m >>= k) = (m' >>= k') := by
  subst h1; exact congrArg _ (funext h2)

theorem eq_bind_pure {α β : Type} {m : EncM α} {a : α} {k : α → EncM β} {m'' : EncM β}
    (h1 : m = pure a) (h2 : k a = m'') : (m >>= k) = m'' := by
  subst h1; rw [pure_bind]; exact h2

theorem eq_pyCall {α : Type} {b : Nat} {k : Nat → EncM α} {m' : EncM α} (hb : 0 < b)
    (h : k (b - 1) = m') : pyCall b k = m' := by
  unfold pyCall; rw [if_neg (by omega)]; exact h

theorem eq_cEnter {c : Nat} {k : Nat → EncM Unit} {m' : EncM Unit} (hc : 0 < c)
    (h : k (c - 1) = m') : cEnter c k = m' := by
  unfold cEnter; rw [if_neg (by omega)]; exact h

theorem eq_ite {α : Type} {c : Prop} [Decidable c] {a b a' b' : EncM α} (h1 : c → a = a')
    (h2 : ¬ c → b = b') : (if c then a else b) = (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem eq_opt {α : Type} {o : Option Nat} {f f' : Nat → EncM α} {g g' : EncM α}
    (h1 : ∀ i, f i = f' i) (h2 : g = g') :
    (match o with | some i => f i | none => g) = (match o with | some i => f' i | none => g') := by
  cases o with
  | some i => exact h1 i
  | none => exact h2

/-! ## Python -/

theorem ex_pyW {b : Nat} (hb : 1 ≤ b) (d : Bytes) : pyW b d = wr d := eq_pyCall hb rfl
theorem ex_commit {b : Nat} (hb : 1 ≤ b) : pyCommitR b = emit .boundary := eq_pyCall hb rfl
theorem ex_pers {b : Nat} (hb : 1 ≤ b) : pyPersR b = pure () := eq_pyCall hb rfl

theorem ex_large {b : Nat} (hb : 2 ≤ b) (p : Nat) (h d : Bytes) : pyLargeR b p h d = emit (.large h d) := by
  refine eq_pyCall (by omega) ?_
  split
  · exact eq_pyCall (by omega) rfl
  · rfl

theorem ex_get {b : Nat} (hb : 1 ≤ b) (p i : Nat) : pyGetR b p i = liftPy (pyGet p i) := eq_pyCall hb rfl

theorem ex_getw {b : Nat} (hb : 1 ≤ b) (p i : Nat) :
    (pyGetR b p i >>= fun d => pyW b d) = (liftPy (pyGet p i) >>= fun d => wr d) :=
  eq_bind (ex_get hb p i) fun d => ex_pyW hb d

theorem ex_memoize {b : Nat} (hb : 2 ≤ b) (p : Nat) (o : Oid) : pyMemoizeR b p o = pyMemoize p o :=
  eq_pyCall (by omega) <| eq_bind rfl fun _ =>
    eq_bind (eq_pyCall (by omega) rfl) fun d => eq_bind (ex_pyW (by omega) d) fun _ => rfl

theorem ex_optWr {b : Nat} (hb : 1 ≤ b) (c : Prop) [Decidable c] (d : Bytes) : optWrR b c d = optWr c d :=
  eq_ite (fun _ => ex_pyW hb d) (fun _ => rfl)

theorem ex_emptyOp {b : Nat} (hb : 1 ≤ b) (p : Nat) (e o : UInt8) : pyEmptyOpR b p e o = pyEmptyOp p e o :=
  eq_ite (fun _ => ex_pyW hb _) (fun _ => ex_pyW hb _)

theorem ex_batchStep {b : Nat} (hb : 1 ≤ b) (p n i : Nat) {it it' : EncM Unit} (h : it = it') (one many : UInt8) :
    pyBatchStepR b p n i it one many = pyBatchStep p n i it' one many :=
  eq_ite (fun _ => eq_bind h fun _ => ex_pyW hb _)
    (fun _ => eq_bind (ex_optWr hb _ _) fun _ => eq_bind h fun _ => ex_optWr hb _ _)

theorem ex_addStep {b : Nat} (hb : 1 ≤ b) (n i : Nat) {it it' : EncM Unit} (h : it = it') :
    addStepR b n i it = addStep n i it' :=
  eq_bind (ex_optWr hb _ _) fun _ => eq_bind h fun _ => ex_optWr hb _ _

theorem ex_saveLong {b : Nat} (hb : 1 ≤ b) (p : Nat) (i : Int) :
    pySaveLongR b p i = (liftPy (pySaveLong p i) >>= fun d => wr d) := by
  have h1 : pySaveLongR.pyEncodeLongR b p i = pure () := by
    unfold pySaveLongR.pyEncodeLongR
    split
    · exact eq_pyCall hb rfl
    · rfl
  exact eq_bind_pure h1 (eq_bind rfl fun d => ex_pyW hb d)

theorem ex_strData {b : Nat} (hb : 2 ≤ b) (p : Nat) (d : Bytes) : pyStrDataR b p d = pyStrData p d :=
  eq_ite (fun _ => ex_pyW (by omega) _) fun _ => eq_ite (fun _ => ex_large hb _ _ _) fun _ =>
    eq_ite (fun _ => eq_bind rfl fun _ => ex_large hb _ _ _) (fun _ => eq_bind rfl fun _ => ex_pyW (by omega) _)

theorem ex_strBody {b : Nat} (hb : 2 ≤ b) (p : Nat) (s : List Nat) : pyStrBodyR b p s = pyStrBody p s :=
  eq_ite (fun _ => ex_strData hb _ _) (fun _ => ex_pyW (by omega) _)

theorem ex_saveStr {b : Nat} (hb : 2 ≤ b) (p : Nat) (o : Oid) (s : List Nat) :
    pySaveStrR b p o s = pySaveStr p o s :=
  eq_bind (ex_strBody hb _ _) fun _ => ex_memoize hb _ _

theorem ex_head {b : Nat} (hb : 1 ≤ b) (p : Nat) (o : Oid) {body body' : EncM Unit} (h : body = body') :
    pySaveHead b p o body = uHead p o body' :=
  eq_bind (ex_commit hb) fun _ => eq_bind_pure (ex_pers hb) <|
    eq_bind rfl fun _ => eq_opt (fun i => ex_getw hb p i) h

theorem ex_strObj {b : Nat} (hb : 4 ≤ b) (p : Nat) (o : Oid) (s : List Nat) :
    pySaveStrObjR b p o s = pySaveStrObj p o s :=
  eq_pyCall (by omega) <| ex_head (by omega) _ _ (eq_pyCall (by omega) (ex_saveStr (by omega) _ _ _))

theorem ex_globalBody {b : Nat} (hb : 4 ≤ b) (p : Nat) (g : Glob) :
    pySaveGlobalBodyR b p g = (do pyGlobalRef p g; pyMemoize p (.glob g)) := by
  have h : pySaveGlobalBodyR.pyGlobalRefR b p g = pyGlobalRef p g := by
    unfold pySaveGlobalBodyR.pyGlobalRefR pyGlobalRef
    split
    · exact eq_bind (ex_strObj hb _ _ _) fun _ => eq_bind (ex_strObj hb _ _ _) fun _ => ex_pyW (by omega) _
    · exact eq_pyCall (by omega) <| eq_bind (ex_pyW (by omega) _) fun _ => ex_pyW (by omega) _
  exact eq_bind_pure (eq_pyCall (by omega) (eq_pyCall (by omega) rfl)) <|
    eq_bind h fun _ => ex_memoize (by omega) _ _

theorem ex_global {b : Nat} (hb : 7 ≤ b) (p : Nat) (g : Glob) : pySaveGlobalR b p g = pySaveGlobal p g := by
  refine eq_pyCall (by omega) <| ex_head (by omega) _ _ ?_
  by_cases hg : g = .codecsEncode
  · rw [if_pos hg]; exact eq_pyCall (by omega) (ex_globalBody (by omega) _ _)
  · rw [if_neg hg]; exact eq_pyCall (by omega) (eq_pyCall (by omega) (ex_globalBody (by omega) _ _))

theorem ex_tupleWith {b : Nat} (hb : 2 ≤ b) (p n : Nat) (o : Oid) {e e' : EncM Unit} (h : e = e') :
    pyTupleWithR b p o n e = pyTupleWith p o n e' := by
  unfold pyTupleWithR pyTupleWith
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
    exact eq_ite (fun _ => ex_pyW (by omega) _) (fun _ => ex_pyW (by omega) _)
  rw [if_neg h0, if_neg h0]
  by_cases h3 : n ≤ 3 ∧ p ≥ 2
  · rw [if_pos h3, if_pos h3]
    refine eq_bind h fun _ => eq_bind rfl fun _ => eq_opt (fun i => ?_) ?_
    · exact eq_bind (ex_get (by omega) _ _) fun _ => ex_pyW (by omega) _
    · exact eq_bind (ex_pyW (by omega) _) fun _ => ex_memoize hb _ _
  · rw [if_neg h3, if_neg h3]
    refine eq_bind (ex_pyW (by omega) _) fun _ => eq_bind h fun _ => eq_bind rfl fun _ => eq_opt (fun i => ?_) ?_
    · exact eq_ite (fun _ => eq_bind (ex_get (by omega) _ _) fun _ => ex_pyW (by omega) _)
        (fun _ => eq_bind (ex_get (by omega) _ _) fun _ => ex_pyW (by omega) _)
    · exact eq_bind (ex_pyW (by omega) _) fun _ => ex_memoize hb _ _

/-- `elems` runs in `save_tuple`'s frame, two below the caller of `save(t)`. -/
theorem ex_tupleObj {b : Nat} (hb : 4 ≤ b) (p n : Nat) (o : Oid) {e : Nat → EncM Unit} {e' : EncM Unit}
    (h : e (b - 1 - 1) = e') : pyTupleObjR b p o n e = pyTupleObj p o n e' :=
  eq_pyCall (by omega) <| ex_head (by omega) _ _ (eq_pyCall (by omega) (ex_tupleWith (by omega) _ _ _ h))

/-- `args` runs in `save_reduce`'s frame, one below its caller. -/
theorem ex_reduce {b : Nat} (hb : 8 ≤ b) (p : Nat) (o : Oid) (g : Glob) {a : Nat → EncM Unit} {a' : EncM Unit}
    (h : a (b - 1) = a') : pyReduceWithR b p o g a = pyReduceWith p o g a' :=
  eq_pyCall (by omega) <| eq_bind (ex_global (by omega) _ _) fun _ => eq_bind h fun _ =>
    eq_bind (ex_pyW (by omega) _) fun _ => eq_bind rfl fun _ =>
      eq_opt (fun i => eq_bind (ex_get (by omega) _ _) fun _ => ex_pyW (by omega) _) (ex_memoize (by omega) _ _)

theorem ex_bytesObj {b : Nat} (hb : 10 ≤ b) (p : Nat) (o : Oid) (d : Bytes) :
    pySaveBytesObjR b p o d = pySaveBytesObj p o d := by
  refine eq_pyCall (by omega) <| ex_head (by omega) _ _ (eq_pyCall (by omega) ?_)
  refine eq_ite (fun _ => eq_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => ?_)
  · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _ rfl)
  · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _
      (eq_bind (ex_strObj (by omega) _ _ _) fun _ => ex_strObj (by omega) _ _ _))
  · exact eq_bind (eq_pyCall (by omega) (eq_ite (fun _ => ex_pyW (by omega) _) fun _ =>
      eq_ite (fun _ => ex_large (by omega) _ _ _) fun _ =>
        eq_ite (fun _ => eq_bind rfl fun _ => ex_large (by omega) _ _ _)
          (fun _ => eq_bind rfl fun _ => ex_pyW (by omega) _))) fun _ => ex_memoize (by omega) _ _

theorem ex_bytearrayObj {b : Nat} (hb : 15 ≤ b) (p : Nat) (o : Oid) (d : Bytes) :
    pySaveBytearrayObjR b p o d = pySaveBytearrayObj p o d := by
  refine eq_pyCall (by omega) <| ex_head (by omega) _ _ (eq_pyCall (by omega) ?_)
  refine eq_ite (fun _ => eq_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => ?_)
  · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _ rfl)
  · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _ (ex_bytesObj (by omega) _ _ _))
  · exact eq_bind (eq_pyCall (by omega) (eq_ite (fun _ => ex_large (by omega) _ _ _)
      (fun _ => ex_pyW (by omega) _))) fun _ => ex_memoize (by omega) _ _

theorem ex_listWith {b : Nat} (hb : 2 ≤ b) (p : Nat) (o : Oid) {it : Nat → EncM Unit} {it' : EncM Unit}
    (h : it (b - 1) = it') : pyListWithR b p o it = pyListWith p o it' :=
  eq_bind (ex_emptyOp (by omega) _ _ _) fun _ => eq_bind (ex_memoize hb _ _) fun _ => eq_pyCall (by omega) h

theorem ex_tmpList {b : Nat} (hb : 4 ≤ b) (p : Nat) (o : Oid) (xs : List PV) {it : Nat → EncM Unit}
    {it' : EncM Unit} (h : it (b - 1 - 1 - 1) = it') :
    pyTmpListR b p o xs it = (do emit .boundary; pyListWith p o it') :=
  eq_pyCall (by omega) <| eq_bind (ex_commit (by omega)) fun _ => eq_bind_pure (ex_pers (by omega)) <|
    eq_pyCall (by omega) (ex_listWith (by omega) _ _ h)

theorem dep_le_list {x : PV} {xs : List PV} (h : x ∈ xs) : x.dep ≤ PV.depL xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rw [PV.depL]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

mutual
theorem ex_save (b p : Nat) : (x : PV) → 10 * x.dep + 16 ≤ b → pySaveR b p x = pySave p x
  | .none, hb => by
    rw [pySaveR, pySave]
    exact eq_pyCall (by omega) <| eq_bind (ex_commit (by omega)) fun _ => eq_bind_pure (ex_pers (by omega)) <|
      eq_pyCall (by omega) (ex_pyW (by omega) _)
  | .bool v, hb => by
    rw [pySaveR, pySave]
    exact eq_pyCall (by omega) <| eq_bind (ex_commit (by omega)) fun _ => eq_bind_pure (ex_pers (by omega)) <|
      eq_pyCall (by omega) (eq_ite (fun _ => ex_pyW (by omega) _) (fun _ => ex_pyW (by omega) _))
  | .int i, hb => by
    rw [pySaveR, pySave]
    exact eq_pyCall (by omega) <| eq_bind (ex_commit (by omega)) fun _ => eq_bind_pure (ex_pers (by omega)) <|
      eq_pyCall (by omega) (ex_saveLong (by omega) _ _)
  | .str o s, hb => by rw [pySaveR, pySave]; exact ex_strObj (by omega) _ _ _
  | .bytes o d, hb => by rw [pySaveR, pySave]; exact ex_bytesObj (by omega) _ _ _
  | .bytearray o d, hb => by rw [pySaveR, pySave]; exact ex_bytearrayObj (by omega) _ _ _
  | .tuple o xs, hb => by
    rw [pySaveR, pySave]
    simp only [PV.dep] at hb
    exact ex_tupleObj (by omega) _ _ _ (ex_elems _ _ xs (by omega))
  | .list o xs, hb => by
    rw [pySaveR, pySave]
    simp only [PV.dep] at hb
    exact eq_pyCall (by omega) <| ex_head (by omega) _ _ <| eq_pyCall (by omega) <|
      ex_listWith (by omega) _ _ (ex_appends _ _ _ _ xs (by omega))
  | .dict o kvs, hb => by
    rw [pySaveR, pySave]
    simp only [PV.dep] at hb
    exact eq_pyCall (by omega) <| ex_head (by omega) _ _ <| eq_pyCall (by omega) <|
      eq_bind (ex_emptyOp (by omega) _ _ _) fun _ => eq_bind (ex_memoize (by omega) _ _) fun _ =>
        eq_pyCall (by omega) (ex_setitems _ _ _ _ kvs (by omega))
  | .set o xs, hb => by
    rw [pySaveR, pySave]
    simp only [PV.dep] at hb
    refine eq_pyCall (by omega) <| ex_head (by omega) _ _ <| eq_pyCall (by omega) <|
      eq_ite (fun _ => ?_) (fun _ => ?_)
    · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _
        (ex_tmpList (by omega) _ _ _ (ex_appends _ _ _ _ xs (by omega))))
    · exact eq_bind (ex_pyW (by omega) _) fun _ => eq_bind (ex_memoize (by omega) _ _) fun _ =>
        ex_additems _ _ _ _ xs (by omega)
  | .frozenset o xs, hb => by
    rw [pySaveR, pySave]
    simp only [PV.dep] at hb
    refine eq_pyCall (by omega) <| ex_head (by omega) _ _ <| eq_pyCall (by omega) <|
      eq_ite (fun _ => ?_) (fun _ => ?_)
    · exact ex_reduce (by omega) _ _ _ (ex_tupleObj (by omega) _ _ _
        (ex_tmpList (by omega) _ _ _ (ex_appends _ _ _ _ xs (by omega))))
    · exact eq_bind (ex_pyW (by omega) _) fun _ => eq_bind (ex_elems _ _ xs (by omega)) fun _ =>
        eq_bind rfl fun _ => eq_opt
          (fun i => eq_bind (ex_get (by omega) _ _) fun _ => ex_pyW (by omega) _)
          (eq_bind (ex_pyW (by omega) _) fun _ => ex_memoize (by omega) _ _)

theorem ex_elems (b p : Nat) : (xs : List PV) → 10 * PV.depL xs + 16 ≤ b → pySaveElemsR b p xs = pySaveElems p xs
  | [], _ => by rw [pySaveElemsR, pySaveElems]
  | x :: xs, hb => by
    rw [pySaveElemsR, pySaveElems]
    simp only [PV.depL] at hb
    exact eq_bind (ex_save b p x (by omega)) fun _ => ex_elems b p xs (by omega)

theorem ex_appends (b p n i : Nat) : (xs : List PV) → 10 * PV.depL xs + 16 ≤ b →
    pyAppendsR b p n i xs = pyAppends p n i xs
  | [], _ => by rw [pyAppendsR, pyAppends]
  | x :: xs, hb => by
    rw [pyAppendsR, pyAppends]
    simp only [PV.depL] at hb
    exact eq_bind (ex_batchStep (by omega) _ _ _ (ex_save b p x (by omega)) _ _) fun _ =>
      ex_appends b p n (i + 1) xs (by omega)

theorem ex_setitems (b p n i : Nat) : (kvs : List (PV × PV)) → 10 * PV.depP kvs + 16 ≤ b →
    pySetitemsR b p n i kvs = pySetitems p n i kvs
  | [], _ => by rw [pySetitemsR, pySetitems]
  | (k, v) :: kvs, hb => by
    rw [pySetitemsR, pySetitems]
    simp only [PV.depP] at hb
    exact eq_bind (ex_batchStep (by omega) _ _ _
        (eq_bind (ex_save b p k (by omega)) fun _ => ex_save b p v (by omega)) _ _) fun _ =>
      ex_setitems b p n (i + 1) kvs (by omega)

theorem ex_additems (b p n i : Nat) : (xs : List PV) → 10 * PV.depL xs + 16 ≤ b →
    pyAdditemsR b p n i xs = pyAdditems p n i xs
  | [], _ => by rw [pyAdditemsR, pyAdditems]
  | x :: xs, hb => by
    rw [pyAdditemsR, pyAdditems]
    simp only [PV.depL] at hb
    exact eq_bind (ex_addStep (by omega) _ _ (ex_save b p x (by omega))) fun _ =>
      ex_additems b p n (i + 1) xs (by omega)
end

theorem ex_body {b : Nat} (p : Nat) (x : PV) (hb : 10 * x.dep + 16 ≤ b) : pyBodyR b p x = pyBody p x := by
  have tail : (do pySaveR b p x; pyW b [oSTOP]; pyCall b fun b' => if p ≥ 4 then pyCall b' (fun _ => emit .finish) else emit .finish)
      = (do pySave p x; wr [oSTOP]; emit .finish) := by
    refine eq_bind (ex_save _ _ _ hb) fun _ => eq_bind (ex_pyW (by omega) _) fun _ => eq_pyCall (by omega) ?_
    split
    · exact eq_pyCall (by omega) rfl
    · rfl
  unfold pyBodyR pyBody
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;> simp only [h2, h4, if_true, if_false] at tail ⊢ <;>
    first
    | exact eq_bind (ex_pyW (by omega) _) fun _ => eq_bind (eq_pyCall (by omega) rfl) fun _ => tail
    | exact eq_bind (ex_pyW (by omega) _) fun _ => tail
    | exact eq_bind (eq_pyCall (by omega) rfl) fun _ => tail
    | exact tail
    | omega

/-! ## C -/

theorem xc_global {c : Nat} (hc : 1 ≤ c) (p : Nat) (g : Glob) : cSaveGlobalR c p g = cSaveGlobal p g :=
  eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter hc rfl)

theorem xc_tupleWith (p n : Nat) (o : Oid) {e e' : EncM Unit} (h : e = e') :
    cTupleWith p o n e = cTupleWith p o n e' := by rw [h]

theorem xc_tupleObj {c : Nat} (hc : 1 ≤ c) (p n : Nat) (o : Oid) {e : Nat → EncM Unit} {e' : EncM Unit}
    (h : e (c - 1) = e') : cTupleObjR c p o n e = cTupleObj p o n e' :=
  eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter hc (xc_tupleWith _ _ _ h))

theorem xc_reduce {c : Nat} (hc : 1 ≤ c) (p : Nat) (o : Oid) (g : Glob) {a a' : EncM Unit} (h : a = a') :
    cReduceWithR c p o g a = cReduceWith p o g a' :=
  eq_bind (xc_global hc _ _) fun _ => eq_bind h fun _ => rfl

theorem xc_bytesObj {c : Nat} (hc : 1 ≤ c) (p : Nat) (o : Oid) (d : Bytes) :
    cSaveBytesObjR c p o d = cSaveBytesObj p o d := by
  refine eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) ?_
  refine eq_ite (fun _ => eq_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => rfl)
  · exact xc_reduce hc _ _ _ (xc_tupleObj hc _ _ _ rfl)
  · exact xc_reduce hc _ _ _ (xc_tupleObj hc _ _ _ rfl)

theorem xc_bytearrayObj {c : Nat} (hc : 3 ≤ c) (p : Nat) (o : Oid) (d : Bytes) :
    cSaveBytearrayObjR c p o d = cSaveBytearrayObj p o d := by
  refine eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter (by omega) ?_)
  refine eq_ite (fun _ => eq_ite (fun _ => ?_) (fun _ => ?_)) (fun _ => rfl)
  · exact xc_reduce (by omega) _ _ _ (xc_tupleObj (by omega) _ _ _ rfl)
  · exact xc_reduce (by omega) _ _ _ (xc_tupleObj (by omega) _ _ _ (xc_bytesObj (by omega) _ _ _))

theorem xc_listWith (p n : Nat) (o : Oid) {it it' : EncM Unit} (h : it = it') :
    cListWith p o n it = cListWith p o n it' := by rw [h]

theorem xc_tmpList {c : Nat} (hc : 2 ≤ c) (p n : Nat) (o : Oid) {it : Nat → EncM Unit} {it' : EncM Unit}
    (h : it (c - 1 - 1) = it') : cTmpListR c p o n it = (do emit .boundary; cListWith p o n it') :=
  eq_bind rfl fun _ => eq_cEnter (by omega) (xc_listWith _ _ _ (eq_cEnter (by omega) h))

mutual
theorem xc_save (c p : Nat) : (x : PV) → 4 * x.dep + 4 ≤ c → cSaveR c p x = cSave p x
  | .none, _ => by rw [cSaveR, cSave]
  | .bool v, _ => by rw [cSaveR, cSave]
  | .int i, _ => by rw [cSaveR, cSave]
  | .str o s, _ => by rw [cSaveR, cSave]
  | .bytes o d, hc => by rw [cSaveR, cSave]; exact xc_bytesObj (by omega) _ _ _
  | .bytearray o d, hc => by rw [cSaveR, cSave]; exact xc_bytearrayObj (by omega) _ _ _
  | .tuple o xs, hc => by
    rw [cSaveR, cSave]
    simp only [PV.dep] at hc
    exact xc_tupleObj (by omega) _ _ _ (xc_elems _ _ xs (by omega))
  | .list o xs, hc => by
    rw [cSaveR, cSave]
    simp only [PV.dep] at hc
    exact eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter (by omega)
      (xc_listWith _ _ _ (eq_cEnter (by omega) (xc_appends _ _ _ _ xs (by omega)))))
  | .dict o kvs, hc => by
    rw [cSaveR, cSave]
    simp only [PV.dep] at hc
    refine eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter (by omega) ?_)
    exact eq_bind rfl fun _ => eq_bind rfl fun _ =>
      eq_ite (fun _ => eq_cEnter (by omega) (xc_setitems _ _ _ _ kvs (by omega))) (fun _ => rfl)
  | .set o xs, hc => by
    rw [cSaveR, cSave]
    simp only [PV.dep] at hc
    refine eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter (by omega) ?_)
    refine eq_ite (fun _ => ?_) (fun _ => ?_)
    · exact xc_reduce (by omega) _ _ _ (xc_tupleObj (by omega) _ _ _
        (xc_tmpList (by omega) _ _ _ (xc_appends _ _ _ _ xs (by omega))))
    · exact eq_bind rfl fun _ => eq_bind rfl fun _ =>
        eq_ite (fun _ => xc_additems _ _ _ _ xs (by omega)) (fun _ => rfl)
  | .frozenset o xs, hc => by
    rw [cSaveR, cSave]
    simp only [PV.dep] at hc
    refine eq_bind rfl fun _ => eq_bind rfl fun _ => eq_opt (fun _ => rfl) (eq_cEnter (by omega) ?_)
    refine eq_ite (fun _ => ?_) (fun _ => ?_)
    · exact xc_reduce (by omega) _ _ _ (xc_tupleObj (by omega) _ _ _
        (xc_tmpList (by omega) _ _ _ (xc_appends _ _ _ _ xs (by omega))))
    · exact eq_bind rfl fun _ => eq_bind (xc_elems _ _ xs (by omega)) fun _ => rfl

theorem xc_elems (c p : Nat) : (xs : List PV) → 4 * PV.depL xs + 4 ≤ c → cSaveElemsR c p xs = cSaveElems p xs
  | [], _ => by rw [cSaveElemsR, cSaveElems]
  | x :: xs, hc => by
    rw [cSaveElemsR, cSaveElems]
    simp only [PV.depL] at hc
    exact eq_bind (xc_save c p x (by omega)) fun _ => xc_elems c p xs (by omega)

theorem xc_appends (c p n i : Nat) : (xs : List PV) → 4 * PV.depL xs + 4 ≤ c →
    cAppendsR c p n i xs = cAppends p n i xs
  | [], _ => by rw [cAppendsR, cAppends]
  | x :: xs, hc => by
    rw [cAppendsR, cAppends]
    simp only [PV.depL] at hc
    rw [xc_save c p x (by omega), xc_appends c p n (i + 1) xs (by omega)]

theorem xc_setitems (c p n i : Nat) : (kvs : List (PV × PV)) → 4 * PV.depP kvs + 4 ≤ c →
    cSetitemsR c p n i kvs = cSetitems p n i kvs
  | [], _ => by rw [cSetitemsR, cSetitems]
  | (k, v) :: kvs, hc => by
    rw [cSetitemsR, cSetitems]
    simp only [PV.depP] at hc
    rw [xc_save c p k (by omega), xc_save c p v (by omega), xc_setitems c p n (i + 1) kvs (by omega)]

theorem xc_additems (c p n i : Nat) : (xs : List PV) → 4 * PV.depL xs + 4 ≤ c →
    cAdditemsR c p n i xs = cAdditems p n i xs
  | [], _ => by rw [cAdditemsR, cAdditems]
  | x :: xs, hc => by
    rw [cAdditemsR, cAdditems]
    simp only [PV.depL] at hc
    rw [xc_save c p x (by omega), xc_additems c p n (i + 1) xs (by omega)]
end

theorem xc_body {c : Nat} (p : Nat) (x : PV) (hc : 4 * x.dep + 4 ≤ c) : cBodyR c p x = cBody p x := by
  unfold cBodyR cBody
  rw [xc_save c p x hc]

end PyLean.Pickle
