import PyLean.Itertools.Simple
import PyLean.Itertools.CombProps

/-!
`batched`: the C object against the doc equivalent (which uses the C `islice`).
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type}

local notation "D" => docIsliceLoop

theorem D_take (B : Int) (err : Option PyExc) : ∀ (xs : List α) (i : Int),
    D (some B) 1 err i i xs =
      (xs.take (B - i).toNat, min xs.length (B - i).toNat,
        if (B - i).toNat ≤ xs.length then none else err)
  | [], i => by
    by_cases h : B ≤ i
    · rw [D_stop B 1 err i i _ h]
      simp [show (B - i).toNat = 0 by omega]
    · rw [D_nil (some B) 1 err i i (by simp [BoundAbove]; omega)]
      have : ¬ (B - i).toNat ≤ 0 := by omega
      simp [this]
  | x :: xs, i => by
    by_cases h : B ≤ i
    · rw [D_stop B 1 err i i _ h]
      simp [show (B - i).toNat = 0 by omega]
    · rw [D_yield (some B) 1 err i x xs (by simp [BoundAbove]; omega), D_take B err xs (i + 1)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (B - i).toNat = k + 1 := ⟨(B - i).toNat - 1, by omega⟩
      rw [hk, show (B - (i + 1)).toNat = k by omega]
      simp <;> omega

/-- `islice(it, n)` for `1 <= n <= sys.maxsize` takes `min(n, len)` items, and
raises the input's exception if it pulls past the last item. -/
theorem cIslice_stop (it : List α) (err : Option PyExc) (n : Int) (h1 : 1 ≤ n) (h2 : n ≤ ssizeMax) :
    cIslice (.iter it err) [some n] =
      ((it.take n.toNat, if n.toNat ≤ it.length then none else err), min (it.length : Int) n) := by
  have hok : IsliceArgsOk [some n] := by simp [IsliceArgsOk]
  have hs : IsliceArgsSsize [some n] := by
    simp [IsliceArgsSsize, InSsize]; rw [ssizeMin_eq] at *; rw [ssizeMax_eq] at *; omega
  have hc := c_args_ok [some n] hok hs (by simp [IsliceRefOk, isliceRef, StopOk]; omega)
  simp only [isliceRef, Option.getD] at hc
  have hmax : (0 : Int) ≤ ssizeMax := by decide
  have hone : (1 : Int) ≤ ssizeMax := by decide
  have hr := cRun_some err (it.length + 1) it 0 0 0 n 1 (by omega) (by omega) (by omega) hmax (by omega) h2
    (by omega) hone (Or.inl rfl)
  rw [show max 0 n = n by omega, D_take n err it 0, show n - 0 = n by omega] at hr
  simp only [cIslice, cIsliceNew, hc, getIter, Obj.len]
  rw [hr.1, hr.2]
  simp only [Prod.mk.injEq, true_and]
  push_cast
  omega

theorem batchedLoop_eq (n : Int) (strict : Bool) (err : Option PyExc) (h1 : 1 ≤ n) (h2 : n ≤ ssizeMax)
    (ht : tupleNewOk n = true) : ∀ (fuel : Nat) (it : List α),
    drain cBatchedNext fuel { it := ⟨it, err⟩, batchSize := n, strict := strict } =
      docBatchedLoop n strict err fuel it
  | 0, _ => rfl
  | fuel + 1, it => by
    rw [drain_succ]
    simp only [cBatchedNext, docBatchedLoop, show ¬ n < 0 by omega, ↓reduceIte, ht, Bool.not_true,
      Bool.false_eq_true, cIslice_stop it err n h1 h2]
    have hd : it.drop (min (it.length : Int) n).toNat = it.drop n.toNat := by
      by_cases hc : (it.length : Int) ≤ n
      · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      · congr 1; omega
    by_cases hfull : ((it.take n.toNat).length : Int) = n
    · have hle : n.toNat ≤ it.length := by simp at hfull; omega
      have hne : it.take n.toNat ≠ [] := by intro h; rw [h] at hfull; simp at hfull; omega
      simp only [hfull, ↓reduceIte, hle, hne, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, hd,
        Run.cons]
      rw [batchedLoop_eq n strict err h1 h2 ht fuel _]
    · have hlt : ¬ n.toNat ≤ it.length := by simp at hfull; omega
      simp only [hfull, ↓reduceIte, hlt]
      cases err with
      | some e => rfl
      | none =>
        by_cases hz : (it.take n.toNat).length = 0
        · have : it.take n.toNat = [] := List.eq_nil_of_length_eq_zero hz
          simp [hz, this, Run.ok]
        · have hne : it.take n.toNat ≠ [] := by intro h; rw [h] at hz; simp at hz
          simp only [hz, ↓reduceIte, hne]
          cases strict with
          | true =>
            simp only [List.length_take] at hfull
            simp [hfull, Run.err]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, hd, Run.cons]
            rw [batchedLoop_eq n false none h1 h2 ht fuel _]

/-- Broad: for every int `n`, C `batched` yields the doc equivalent's batches
and raises in the same cases, over any element type and input object. -/
def BatchedDocAgree : Prop :=
  ∀ (α : Type) (o : Obj α) (n : Int) (strict : Bool), runAgree (cBatched o n strict) (docBatched o n strict)

theorem batchedDocAgree_refuted : ¬BatchedDocAgree := by
  intro h
  have := (h Int (.iter [1, 2, 3] none) (2 ^ 63 - 1) false).1
  revert this
  decide

/-- Narrowed to `n` for which a result tuple of `n` items can be allocated. -/
def BatchedDocAgreeAlloc : Prop :=
  ∀ (α : Type) (o : Obj α) (n : Int) (strict : Bool), tupleNewOk n = true →
    runAgree (cBatched o n strict) (docBatched o n strict)

theorem batchedDocAgreeAlloc_proven : BatchedDocAgreeAlloc := by
  intro α o n strict ht
  by_cases h1 : n < 1
  · have hc : ∃ e, cBatched o n strict = Run.err e := by
      simp only [cBatched, cBatchedNew]
      cases ha : asSsize n with
      | error e => exact ⟨e, rfl⟩
      | ok v =>
        have hv : v = n := by simp only [asSsize] at ha; split at ha <;> simp_all
        subst hv
        exact ⟨.valueError "n must be at least one", by simp [h1]⟩
    obtain ⟨e, he⟩ := hc
    simp [runAgree, he, docBatched, h1, Run.err]
  · have h2 : n ≤ ssizeMax := by
      simp only [tupleNewOk, ssizeMax_eq, mallocLimit_eq, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        decide_eq_true_eq] at ht ⊢
      omega
    apply runAgree_of_eq
    cases o with
    | notIterable ty =>
      simp [cBatched, cBatchedNew, asSsize_ok (by rw [ssizeMin_eq]; omega) h2, docBatched, h1, getIter]
    | iter l err =>
      simp only [cBatched, cBatchedNew, asSsize_ok (by rw [ssizeMin_eq]; omega) h2, docBatched, h1,
        ↓reduceIte, getIter, Obj.len]
      exact batchedLoop_eq n strict err (by omega) h2 ht _ l

end PyLean.Itertools
