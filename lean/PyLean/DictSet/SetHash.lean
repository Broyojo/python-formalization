import PyLean.DictSet.SetRefine

/-!
`frozenset_hash_impl` folds over every slot, NULL and dummy included, and then takes their effect out
again (`Objects/setobject.c:979-998`). The theorem here is that the result depends only on the active
entries: on their stored hashes and how many there are.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type}

/-- The hash as the comment at :982-984 describes it: only the active entries go in. -/
def frozensetHashOf (hs : List Int) : Int :=
  let h0 := hs.foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0
  let h3 := h0 ^^^ (((hs.length + 1) * 1927868237) % 2 ^ 64)
  let h4 := h3 ^^^ ((h3 >>> 11) ^^^ (h3 >>> 25))
  let h5 := (h4 * 69069 + 907133923) % 2 ^ 64
  let h6 := if h5 == 2 ^ 64 - 1 then 590923713 else h5
  toI64 h6

/-- `x` an odd number of times, xored together. -/
def oddly (n x : Nat) : Nat := if n % 2 == 1 then x else 0

theorem oddly_succ (n x : Nat) : oddly (n + 1) x = oddly n x ^^^ x := by
  simp only [oddly]
  by_cases h : n % 2 = 1
  · have h1 : (n + 1) % 2 ≠ 1 := by omega
    simp [h, h1, Nat.xor_self]
  · have h1 : (n + 1) % 2 = 1 := by omega
    simp [h, h1]

theorem foldl_xor_shift {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun h s => h ^^^ f s) a = a ^^^ l.foldl (fun h s => h ^^^ f s) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [ih, ih (f x), Nat.xor_assoc]

/-- The stored hashes of the active slots, in table order. -/
def activeHashes : List (Slot K) → List Int
  | [] => []
  | .active _ h :: t => h :: activeHashes t
  | _ :: t => activeHashes t

def nullCount : List (Slot K) → Nat
  | [] => 0
  | .null :: t => nullCount t + 1
  | _ :: t => nullCount t

def dummyCount : List (Slot K) → Nat
  | [] => 0
  | .dummy :: t => dummyCount t + 1
  | _ :: t => dummyCount t

/-- Over every slot, the fold is the fold over the active ones and an odd count of the other two. -/
theorem fold_splits (t : List (Slot K)) :
    t.foldl (fun h s => h ^^^ shuffleBits s.hashU) 0 =
      (activeHashes t).foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0 ^^^
        oddly (nullCount t) (shuffleBits 0) ^^^ oddly (dummyCount t) (shuffleBits (toU64 (-1))) := by
  induction t with
  | nil => simp [activeHashes, nullCount, dummyCount, oddly]
  | cons x t ih =>
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [foldl_xor_shift]
    rw [ih]
    cases x with
    | null =>
      simp only [Slot.hashU, activeHashes, nullCount, dummyCount, oddly_succ]
      generalize (activeHashes t).foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0 = A
      generalize oddly (nullCount t) (shuffleBits 0) = B
      generalize oddly (dummyCount t) (shuffleBits (toU64 (-1))) = C
      generalize shuffleBits 0 = D
      ac_rfl
    | dummy =>
      simp only [Slot.hashU, activeHashes, nullCount, dummyCount, oddly_succ]
      generalize (activeHashes t).foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0 = A
      generalize oddly (nullCount t) (shuffleBits 0) = B
      generalize oddly (dummyCount t) (shuffleBits (toU64 (-1))) = C
      generalize shuffleBits (toU64 (-1)) = D
      ac_rfl
    | active k h =>
      simp only [Slot.hashU, activeHashes, nullCount, dummyCount, List.foldl_cons, Nat.zero_xor]
      rw [foldl_xor_shift (fun x => shuffleBits (toU64 x)) (activeHashes t) (shuffleBits (toU64 h))]
      generalize oddly (nullCount t) (shuffleBits 0) = B
      generalize oddly (dummyCount t) (shuffleBits (toU64 (-1))) = C
      generalize (activeHashes t).foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0 = A
      generalize shuffleBits (toU64 h) = D
      ac_rfl

theorem activeHashes_eq (t : List (Slot K)) :
    activeHashes t = (t.filterMap slotEntry).map (·.2) := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    cases x <;> simp [activeHashes, ih]

theorem counts_len (t : List (Slot K)) :
    t.length = nullCount t + dummyCount t + (activeHashes t).length := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    cases x <;> simp [activeHashes, nullCount, dummyCount, ih] <;> omega

theorem counts_fill (t : List (Slot K)) :
    t.countP (fun x => !x.isNull) = dummyCount t + (activeHashes t).length := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    rw [List.countP_cons, ih]
    cases x <;> simp [activeHashes, dummyCount, Slot.isNull] <;> omega

/-- The frozenset hash depends only on the active entries (`setobject.c:982-984`): for a table with
the counts it keeps, whatever NULLs and dummies it holds, it is `frozensetHashOf` of the stored hashes
of the active entries. A version that left the corrections out, or tested the wrong count, would
differ on any table with an odd number of either. -/
def FrozensetHashActive : Prop :=
  ∀ (K : Type) (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K), SetCore hf eqv so →
    frozensetHashImpl so = frozensetHashOf ((setEntries so).map (·.2))
theorem frozensetHashActive_proven : FrozensetHashActive := by
  intro K hf eqv so w
  have hlen := counts_len so.table
  have hfill := counts_fill so.table
  have hused : (activeHashes so.table).length = so.used := by
    rw [w.used, activeHashes_eq, setEntries_eq]
    simp
  have hf1 : so.fill = dummyCount so.table + so.used := by
    rw [w.fill, hfill, hused]
  have hl : so.table.length = so.mask + 1 := w.len
  have hn : so.mask + 1 - so.fill = nullCount so.table := by omega
  have hd : so.fill - so.used = dummyCount so.table := by omega
  have ha : (setEntries so).map (·.2) = activeHashes so.table := by
    rw [activeHashes_eq, setEntries_eq]
  have hlen2 : (activeHashes so.table).length = so.used := hused
  simp only [frozensetHashImpl, frozensetHashOf, ha, hn, hd, hlen2, fold_splits]
  generalize (activeHashes so.table).foldl (fun h x => h ^^^ shuffleBits (toU64 x)) 0 = A
  have e1 : (if nullCount so.table % 2 == 1 then
      A ^^^ oddly (nullCount so.table) (shuffleBits 0) ^^^
        oddly (dummyCount so.table) (shuffleBits (toU64 (-1))) ^^^ shuffleBits 0
    else A ^^^ oddly (nullCount so.table) (shuffleBits 0) ^^^
        oddly (dummyCount so.table) (shuffleBits (toU64 (-1)))) =
      A ^^^ oddly (dummyCount so.table) (shuffleBits (toU64 (-1))) := by
    simp only [oddly]
    by_cases h : nullCount so.table % 2 = 1
    · simp only [h, beq_self_eq_true, if_true]
      rw [Nat.xor_assoc A, Nat.xor_comm (shuffleBits 0), Nat.xor_assoc A, Nat.xor_assoc,
        Nat.xor_self, Nat.xor_zero]
    · simp [h]
  rw [e1]
  have e2 : (if dummyCount so.table % 2 == 1 then
      A ^^^ oddly (dummyCount so.table) (shuffleBits (toU64 (-1))) ^^^ shuffleBits (toU64 (-1))
    else A ^^^ oddly (dummyCount so.table) (shuffleBits (toU64 (-1)))) = A := by
    simp only [oddly]
    by_cases h : dummyCount so.table % 2 = 1
    · simp only [h, beq_self_eq_true, if_true]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · simp [h]
  rw [e2]

/-- Equal sets hash alike, however their tables came to be: `frozenset_hash` of two well-formed
tables with the same stored hashes, in any order. This is what makes frozensets usable as keys. -/
def FrozensetHashEqual : Prop :=
  ∀ (K : Type) (hf : K → Int) (eqv : K → K → Bool) (a b : SetObj K),
    SetCore hf eqv a → SetCore hf eqv b → (setEntries a).Perm (setEntries b) →
    frozensetHashImpl a = frozensetHashImpl b
theorem frozensetHashEqual_proven : FrozensetHashEqual := by
  intro K hf eqv a b wa wb hp
  rw [frozensetHashActive_proven K hf eqv a wa, frozensetHashActive_proven K hf eqv b wb]
  have hq := hp.map (·.2)
  simp only [frozensetHashOf, hq.length_eq]
  rw [foldl_xor_perm (fun x => shuffleBits (toU64 x)) hq]

/-- `frozenset_hash` (:1014-1027): the first call stores the hash, and a stored hash is what any later
call answers, without looking at the table. -/
def FrozensetHashCached : Prop :=
  ∀ (K : Type) (so : SetObj K),
    (so.hash != -1 → frozensetHash so = (so.hash, so)) ∧
    (so.hash = -1 →
      let r := frozensetHash so
      r.1 = frozensetHashImpl so ∧ r.2.hash = r.1 ∧ r.1 ≠ -1 ∧ (frozensetHash r.2).1 = r.1)
theorem frozensetHashCached_proven : FrozensetHashCached := by
  intro K so
  refine ⟨fun h => by simp [frozensetHash, h], fun h => ?_⟩
  have hne := frozensetHashNotMinusOne_proven K so
  simp [frozensetHash, h, hne]

end PyLean.DictSet
