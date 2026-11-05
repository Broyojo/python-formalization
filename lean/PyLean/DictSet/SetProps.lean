import PyLean.DictSet.SetOps

/-!
Exact properties of the set table that hold without the probing invariant: the frozenset hash, the
resize size, `clear`, iteration. The refinement of set probing is in `SetRefine.lean`.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type}

theorem foldl_xor_perm {α : Type} (f : α → Nat) {l l' : List α} (h : l.Perm l') (a : Nat) :
    l.foldl (fun h s => h ^^^ f s) a = l'.foldl (fun h s => h ^^^ f s) a := by
  induction h generalizing a with
  | nil => rfl
  | cons x _ ih => exact ih _
  | swap x y t =>
    simp only [List.foldl_cons]
    rw [Nat.xor_assoc, Nat.xor_comm (f y), ← Nat.xor_assoc]
  | trans _ _ ih1 ih2 => exact (ih1 a).trans (ih2 a)

/-- The frozenset hash does not depend on where entries sit: two tables with the same slots in any
order, the same mask, `fill` and `used`, hash alike (`setobject.c:979-987`: "a frozenset hash should
be independent of order"). -/
def FrozensetHashOrderFree : Prop :=
  ∀ (K : Type) (a b : SetObj K), a.table.Perm b.table → a.mask = b.mask → a.fill = b.fill →
    a.used = b.used → frozensetHashImpl a = frozensetHashImpl b

theorem frozensetHashOrderFree_proven : FrozensetHashOrderFree := by
  intro K a b hp hm hf hu
  have h0 := foldl_xor_perm (fun s : Slot K => shuffleBits s.hashU) hp 0
  simp only [frozensetHashImpl, h0, hm, hf, hu]

/-- `-1` is reserved: the frozenset hash is never the error value (`setobject.c:1007-1009`). -/
def FrozensetHashNotMinusOne : Prop :=
  ∀ (K : Type) (s : SetObj K), frozensetHashImpl s ≠ -1

theorem toI64_ne_neg_one (u : Nat) (hu : u < 2 ^ 64) (h : u ≠ 2 ^ 64 - 1) : toI64 u ≠ -1 := by
  simp only [toI64, Nat.mod_eq_of_lt hu]
  split <;> omega

theorem frozensetHashNotMinusOne_proven : FrozensetHashNotMinusOne := by
  intro K s
  simp only [frozensetHashImpl]
  generalize hh : ((_ : Nat) * 69069 + 907133923) % 2 ^ 64 = h5
  have hlt : h5 < 2 ^ 64 := by rw [← hh]; exact Nat.mod_lt _ (by decide)
  by_cases he : h5 = 2 ^ 64 - 1
  · simp only [he]
    decide
  · have : (h5 == 2 ^ 64 - 1) = false := by simpa using he
    simp only [this, Bool.false_eq_true, if_false]
    exact toI64_ne_neg_one h5 hlt he

/-- `set_table_resize` picks the smallest table above `minused`, up to the 64 doublings a
`size_t` allows. -/
theorem setNewSize_spec (minused : Nat) : ∀ (f n : Nat), 0 < n → minused < n * 2 ^ f →
    minused < setNewSize minused f n ∧ n ≤ setNewSize minused f n ∧
      (∃ k, setNewSize minused f n = n * 2 ^ k) ∧
      (n < setNewSize minused f n → setNewSize minused f n / 2 ≤ minused) := by
  intro f
  induction f with
  | zero =>
    intro n hn h
    simp only [Nat.pow_zero, Nat.mul_one] at h
    exact ⟨by simpa [setNewSize] using h, by simp [setNewSize], ⟨0, by simp [setNewSize]⟩,
      by simp [setNewSize]⟩
  | succ f ih =>
    intro n hn h
    by_cases hle : n ≤ minused
    · have e : setNewSize minused (f + 1) n = setNewSize minused f (n <<< 1) := by
        simp [setNewSize, hle]
      have hs : n <<< 1 = n * 2 := by simp [Nat.shiftLeft_eq]
      rw [e, hs]
      have h' : minused < (n * 2) * 2 ^ f := by
        have : n * 2 ^ (f + 1) = (n * 2) * 2 ^ f := by
          rw [Nat.pow_succ]
          simp [Nat.mul_assoc, Nat.mul_comm]
        omega
      obtain ⟨a, b, ⟨k, c⟩, d⟩ := ih (n * 2) (by omega) h'
      refine ⟨a, by omega, ⟨k + 1, ?_⟩, ?_⟩
      · rw [c, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      · intro _
        by_cases hq : n * 2 < setNewSize minused f (n * 2)
        · exact d hq
        · have : setNewSize minused f (n * 2) = n * 2 := by omega
          rw [this]
          omega
    · have e : setNewSize minused (f + 1) n = n := by
        cases f <;> simp [setNewSize, hle]
      rw [e]
      exact ⟨by omega, by omega, ⟨0, by simp⟩, by omega⟩

/-- The table `set_table_resize` asks for: larger than `minused`, a power of two, and the smallest
such above 8. -/
def SetNewSizeMinimal : Prop :=
  ∀ minused, minused < 2 ^ 63 →
    let s := setNewSize minused 64 PySet_MINSIZE
    minused < s ∧ PySet_MINSIZE ≤ s ∧ (PySet_MINSIZE < s → s / 2 ≤ minused)

theorem setNewSizeMinimal_proven : SetNewSizeMinimal := by
  intro minused h
  obtain ⟨a, b, _, d⟩ := setNewSize_spec minused 64 PySet_MINSIZE (by decide) (by
    simp only [PySet_MINSIZE]
    omega)
  exact ⟨a, b, d⟩

/-- `set.clear()` leaves no entries (`setobject.c:645-694`), and a cleared table has no dummies and
is the small table. Holds when a small table with `fill == 0` holds no entries, which `fill`
counts. -/
def SetClearEmpties : Prop :=
  ∀ (K : Type) (s : SetObj K), (s.tableId = 0 → s.fill = 0 → setEntries s = []) →
    setEntries (setClearInternal s) = [] ∧ (setClearInternal s).used = (if s.tableId != 0 || s.fill > 0 then 0 else s.used)

theorem setClearEmpties_proven : SetClearEmpties := by
  intro K s h
  have hemp : setEntries (setEmptyToMinsize s) = [] := by
    simp [setEntries, setEmptyToMinsize, List.filterMap_replicate]
  by_cases h1 : (s.tableId != 0) = true
  · have e : setClearInternal s = setEmptyToMinsize s := by
      unfold setClearInternal
      rw [if_pos h1]
    rw [e]
    exact ⟨hemp, by simp [h1, setEmptyToMinsize]⟩
  · by_cases h2 : s.fill > 0
    · have e : setClearInternal s = setEmptyToMinsize s := by
        unfold setClearInternal
        rw [if_neg h1, if_pos h2]
      rw [e]
      exact ⟨hemp, by simp [h2, setEmptyToMinsize]⟩
    · have hid : s.tableId = 0 := by simpa using h1
      have hf : s.fill = 0 := by omega
      have e : setClearInternal s = s := by
        unfold setClearInternal
        rw [if_neg h1, if_neg h2]
      rw [e]
      exact ⟨h hid hf, by simp [hid, hf]⟩

/-- The contract of `__hash__` and `__eq__`, for a set's keys. -/
structure HonestSet (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool) : Prop where
  /-- `__hash__` answers `hf k` and changes nothing. -/
  hash_ok : ∀ k s, P.hashM k s = (.ok (hf k), s)
  eq_ok : ∀ a b s, P.eq a b s = (.ok (eqv a b), s)
  str_eq : ∀ a b, P.isStr a = true → P.isStr b = true → P.strEq a b = eqv a b
  refl : ∀ a, eqv a a = true
  symm : ∀ a b, eqv a b = eqv b a
  trans : ∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true
  hash_cons : ∀ a b, eqv a b = true → hf a = hf b

/-- A run of `add` and `discard` from an empty set. -/
inductive SOp (K : Type) where
  | add (k : K)
  | discard (k : K)

def setProg [DecidableEq K] (P : Proto K (SetObj K)) : List (SOp K) → SetObj K → SetObj K
  | [], s => s
  | .add k :: rest, s => setProg P rest (setAddKey P k s).2
  | .discard k :: rest, s => setProg P rest (setDiscardKey P k s).2

def setAbs (eqv : K → K → Bool) : List (SOp K) → List K → List K
  | [], l => l
  | .add k :: rest, l => setAbs eqv rest (if l.any (eqv · k) then l else l ++ [k])
  | .discard k :: rest, l => setAbs eqv rest (l.filter fun x => !eqv x k)

end PyLean.DictSet
